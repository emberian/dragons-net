-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.Server.SessionHost
import DN.News.ArticleRun
import DN.News.AbnfComment

/-!
# DN.Server.SessionIdentity

The identity the session takes from its host's first batch, as `SessionSpec.turn` is given it. `identityTake` takes in
a revision and a source that fit the replies (`Identity.ok`), or stops the run. It keeps one taken
(`identityTake_ok`).
-/

namespace DN.Server.SessionIdentity

open DN.Compiler DN.Compiler.Wp DN.Compiler.Frag DN.Compiler.WpRet DN.News.FunRun DN.Server.SessionLayout
open DN.News.FramerCode (Chunk bw)
open DN.News.CommandSpec (Identity isVisible)
open DN.Server.SessionState (NumW)
open DN.Server.SessionStoreAt (ownW)
open DN.Server.SessionHost (nextW)
open DN.News.ScanRun (at_ vals_lookup Fresh fresh_cons lookup_cons_ne lookup_head without)
open DN.News.FunRun (upd)
open DN.News.ArticleRun (fragR_pure)

variable {σ : Type}

/-- **The batch names identity `i`**: the revision's and the source's lengths, and of each that fits its area, its
octets. -/
def NextIdentity (b : Word) (i : Identity) (s : PancakeState σ) : Prop :=
  (s.memory (nextW b nextRevLen)).toNat = i.revision.length ∧
    (s.memory (nextW b nextSrcLen)).toNat = i.source.length ∧
    (i.revision.length ≤ revMax → Chunk s (nextW b nextRev) i.revision) ∧
    (i.source.length ≤ srcMax → Chunk s (nextW b nextSrc) i.source)

/-- **The program holds identity `i`**: taken in, of a revision and a source that fit the replies. -/
def IdentityAt (b : Word) (i : Identity) (s : PancakeState σ) : Prop :=
  s.memory (ownW b ownReady) = 1 ∧ i.ok = true ∧ NumW s (ownW b ownRevLen) i.revision.length ∧
    Chunk s (ownW b ownRev) i.revision ∧ NumW s (ownW b ownSrcLen) i.source.length ∧
    Chunk s (ownW b ownSrc) i.source

/-- A word `identityTake` may write: the flag, the lengths and the octets' areas. -/
def Took (y : Nat) : Prop := y = ownOff + ownReady ∨ (ownOff + ownRevLen ≤ y ∧ y < ownOff + ownSrc + srcMax)

/-- The state of `s` with memory `m`. -/
def withMem (s : PancakeState σ) (m : Word → Word) : PancakeState σ := { s with memory := m }

/-- What `identityTake` leaves of memory `m`. Words it does not write are as at the entry `s1`. The identity held is
kept, or the batch's taken in. -/
def Kept0 (b : Word) (s1 : PancakeState σ) (m : Word → Word) : Prop :=
  (∀ y, y < 2 ^ 64 → ¬Took y → m (b + BitVec.ofNat 64 y) = s1.memory (b + BitVec.ofNat 64 y)) ∧
    (s1.memory (ownW b ownReady) ≠ 0 ∧ m = s1.memory ∨
      s1.memory (ownW b ownReady) = 0 ∧ ∃ i, NextIdentity b i s1 ∧ IdentityAt b i (withMem s1 m))

/-- **What `identityTake` gives back**: zero, and `Kept0`; or the stop's code, the batch's identity not fitting. -/
def IdRet (b : Word) (s1 : PancakeState σ) : Ret := fun w m =>
  (w = 0 ∧ Kept0 b s1 m) ∨
  (w = BitVec.ofNat 64 badIdentity ∧ m = upd s1.memory (ownW b ownStop) (BitVec.ofNat 64 badIdentity) ∧
    s1.memory (ownW b ownReady) = 0 ∧ ∀ i, NextIdentity b i s1 → i.ok = false)

/-- Octets at one place, as many, are the same. -/
theorem chunk_eq {s : PancakeState σ} {p : Word} {q1 q2 : List DN.News.FrameSpec.Byte} (h1 : Chunk s p q1)
    (h2 : Chunk s p q2) (hl : q1.length = q2.length) : q1 = q2 :=
  List.ext_getElem hl fun i hi1 hi2 => Option.some.inj ((h1 i hi1).symm.trans (h2 i hi2))

/-- An identity of a length the replies do not fit is not one. -/
theorem ok_lengths {i : Identity} (h : ¬(1 ≤ i.revision.length ∧ i.revision.length ≤ revMax ∧
    1 ≤ i.source.length ∧ i.source.length ≤ srcMax)) : i.ok = false := by
  rw [Bool.eq_false_iff]
  intro h'
  rw [SessionLayout.identity_ok] at h'
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h'
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, -⟩, h3⟩, h4⟩, -⟩ := h'
  exact h ⟨h1, h2, h3, h4⟩

/-- An identity with a revision octet not visible is not one. -/
theorem ok_rev {i : Identity} (h : i.revision.all isVisible = false) : i.ok = false := by
  rw [SessionLayout.identity_ok]; simp [h]

/-- An identity with a source octet not visible is not one. -/
theorem ok_src {i : Identity} (h : i.source.all isVisible = false) : i.ok = false := by
  rw [SessionLayout.identity_ok]; simp [h]

/-- An identity of lengths that fit and visible octets is one. -/
theorem ok_of {i : Identity} (h : 1 ≤ i.revision.length ∧ i.revision.length ≤ revMax ∧ 1 ≤ i.source.length ∧
    i.source.length ≤ srcMax) (hr : i.revision.all isVisible = true) (hs : i.source.all isVisible = true) :
    i.ok = true := by
  rw [SessionLayout.identity_ok]
  simp only [hr, hs, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
  omega

/-- **The batch names one identity** once its lengths fit their areas. -/
theorem next_unique {b : Word} {s : PancakeState σ} {i i' : Identity} (hi : NextIdentity b i s)
    (hi' : NextIdentity b i' s) (hr : i.revision.length ≤ revMax) (hs : i.source.length ≤ srcMax) : i' = i := by
  have e1 : i'.revision.length = i.revision.length := by rw [← hi'.1, ← hi.1]
  have e2 : i'.source.length = i.source.length := by rw [← hi'.2.1, ← hi.2.1]
  have r := chunk_eq (hi'.2.2.1 (by omega)) (hi.2.2.1 hr) e1
  have q := chunk_eq (hi'.2.2.2 (by omega)) (hi.2.2.2 hs) e2
  cases i'; cases i
  simp only at r q
  rw [r, q]

/-- Octets at a place, as `appendRevision_frag` and `appendSource_frag` read them. -/
theorem chunk_bytes {s : PancakeState σ} {p : Word} {q : List DN.News.FrameSpec.Byte} (h : Chunk s p q) :
    Bytes.memBytesAt s.memory s.memaddrs s.be p q := fun i hi => by rw [getElem!_pos q i hi]; exact h i hi

/-- The identity held: its revision and its source, each within its area. -/
theorem identityAt_rev {b : Word} {i : Identity} {s : PancakeState σ} (h : IdentityAt b i s) :
    Bytes.memBytesAt s.memory s.memaddrs s.be (ownW b ownRev) i.revision ∧ i.revision.length ≤ revMax := by
  refine ⟨chunk_bytes h.2.2.2.1, ?_⟩
  have := h.2.1; rw [SessionLayout.identity_ok] at this
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this; omega

theorem identityAt_src {b : Word} {i : Identity} {s : PancakeState σ} (h : IdentityAt b i s) :
    Bytes.memBytesAt s.memory s.memaddrs s.be (ownW b ownSrc) i.source ∧ i.source.length ≤ srcMax := by
  refine ⟨chunk_bytes h.2.2.2.2.2, ?_⟩
  have := h.2.1; rw [SessionLayout.identity_ok] at this
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this; omega

/-- **An identity held is kept** by `identityTake`. -/
theorem identity_kept {b : Word} {i : Identity} {s1 : PancakeState σ} {m : Word → Word} (h : IdentityAt b i s1)
    (hk : Kept0 b s1 m) : IdentityAt b i (withMem s1 m) := by
  rcases hk.2 with ⟨-, e⟩ | ⟨h0, -⟩
  · subst e; exact h
  · rw [h.1] at h0; exact absurd h0 (by decide)

/-! ## Reads -/

/-- A word of the session's heap, read at a state of the body. -/
theorem ld_eval {s1 u : PancakeState σ} {b : Word} (hb0 : s1.baseAddr = b)
    (hcov : Analyzer.Covers SessionLayout.size s1.memaddrs b) {l : List (String × Value)} {M : Word → Word}
    (h : RunF s1 l (· = M) u) {X : Nat} (hX8 : X % 8 = 0) (hf : 64 ≤ X) (hX : X < SessionLayout.size) :
    eval u (.loadWord (.op .add .base (.const (BitVec.ofNat 64 X)))) = some (M (b + BitVec.ofNat 64 X)) := by
  have hbase : u.baseAddr = b := h.1.base.trans hb0
  rw [← h.2]
  exact DN.News.ArticleRun.loadA_eval h.1.memaddrs (A := b) (y := X) (hcov.2 X hf hX hX8)
    (by simp only [eval, hbase]; rfl)

/-- **`w < lo || hi < w`**, signed, is `w`'s number outside `[lo, hi]`. -/
theorem out_eval {u : PancakeState σ} {E : PancakeExp} {W : Word} (hE : eval u E = some W) {lo hi : Nat}
    (hlo : lo < 2 ^ 63) (hhi : hi < 2 ^ 63) :
    eval u (DN.News.FramerCode.or2E (.cmp .less E (.const (BitVec.ofNat 64 lo)))
      (.cmp .less (.const (BitVec.ofNat 64 hi)) E)) =
      some (bw (decide (W.toNat < lo ∨ hi < W.toNat))) := by
  by_cases h : W.toNat < 2 ^ 63
  · obtain ⟨w, hw, rfl⟩ : ∃ w, w < 2 ^ 63 ∧ W = BitVec.ofNat 64 w := ⟨W.toNat, h, by simp⟩
    rw [DN.News.FramerCode.eval_or2 (DN.News.FramerCode.eval_lt hw hlo hE rfl)
      (DN.News.FramerCode.eval_lt hhi hw rfl hE),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    by_cases h1 : w < lo <;> by_cases h2 : hi < w <;> simp [h1, h2]
  · have h1 : signedLt W (BitVec.ofNat 64 lo) = true := by
      simp only [signedLt, BitVec.slt, BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, decide_eq_true_eq]
      rw [Nat.mod_eq_of_lt (by omega)]; split <;> split <;> omega
    have h2 : signedLt (BitVec.ofNat 64 hi) W = false := by
      simp only [signedLt, BitVec.slt, BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, decide_eq_false_iff_not]
      rw [Nat.mod_eq_of_lt (by omega)]; split <;> split <;> omega
    simp only [DN.News.FramerCode.or2E, eval, hE, h1, h2]
    rw [show decide (W.toNat < lo ∨ hi < W.toNat) = true by simp; omega]
    rfl

/-- **The batch names an identity**: the octets of each length that fits its area, else any of that length. -/
theorem next_identity {s : PancakeState σ} {b : Word} (hcov : Analyzer.Covers SessionLayout.size s.memaddrs b) :
    ∃ i, NextIdentity b i s := by
  have part : ∀ k max, k + max ≤ nextLen → ∀ L : Nat, ∃ bs : List DN.News.FrameSpec.Byte, bs.length = L ∧
      (L ≤ max → Chunk s (nextW b k) bs) := fun k max hk L => by
    by_cases hL : L ≤ max
    · obtain ⟨ys, hyl, hys⟩ := Bytes.bytes_exist (u := s) (a := nextW b k) L
        (SessionHost.next_bytes hcov (by omega))
      exact ⟨ys, hyl, fun _ => hys⟩
    · exact ⟨List.replicate L 0, by simp, fun h => absurd h hL⟩
  obtain ⟨rv, hrl, hrv⟩ := part nextRev revMax (by decide) (s.memory (nextW b nextRevLen)).toNat
  obtain ⟨sc, hsl, hsc⟩ := part nextSrc srcMax (by decide) (s.memory (nextW b nextSrcLen)).toNat
  exact ⟨⟨rv, sc⟩, hrl.symm, hsl.symm, fun h => hrv (by rw [← hrl]; exact h),
    fun h => hsc (by rw [← hsl]; exact h)⟩

/-- The session's own words before the texts lie within its heap. -/
theorem own_in {x : Nat} (hx : x < ownTexts) : 64 ≤ ownOff + x ∧ ownOff + x < SessionLayout.size := by
  obtain ⟨-, -, -, -, h4, -, h6, -⟩ := areas_disjoint
  have h4' : ownOff + ownTexts ≤ tableOff := Nat.le_trans (Nat.le_add_right _ _) h4
  have h6' : tableOff ≤ SessionLayout.size :=
    Nat.le_trans (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)) h6
  have h0 : 64 ≤ ownOff := by decide
  clear h4 h6
  generalize SessionLayout.size = S at h6' ⊢
  generalize tableOff = T at h4' h6'
  generalize ownTexts = E at h4' hx
  generalize ownOff = O at h0 h4' ⊢
  omega

/-- The session's own words lie past the `dn_next` array, the texts within the heap. -/
theorem own_facts :
    nextOff + nextLen ≤ ownOff ∧ ownOff + ownTexts ≤ SessionLayout.size ∧ ownTexts < 2 ^ 62 := by
  obtain ⟨-, -, h2, h3, h4, -, h6, -⟩ := areas_disjoint
  have h3' : emitOff ≤ ownOff := Nat.le_trans (Nat.le_add_right _ _) h3
  have h4' : ownOff + ownTexts ≤ tableOff := Nat.le_trans (Nat.le_add_right _ _) h4
  have h6' : tableOff ≤ SessionLayout.size :=
    Nat.le_trans (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)) h6
  refine ⟨Nat.le_trans h2 h3', Nat.le_trans h4' h6', by decide⟩

/-! ## Steps -/

/-- **A stop**: its code in the stop word, then given back. -/
theorem stop_frag (o : Oracle σ) {R : Ret} {s1 : PancakeState σ} {b : Word} (hb0 : s1.baseAddr = b)
    (hcov : Analyzer.Covers SessionLayout.size s1.memaddrs b) {l : List (String × Value)} {M : Word → Word}
    {P' : Assn σ} {code : Nat} (hR : R (BitVec.ofNat 64 code) (upd M (ownW b ownStop) (BitVec.ofNat 64 code))) :
    FragR o R (SessionStore.stop code) (RunF s1 l (· = M)) P' := by
  have hst := own_in (x := ownStop) (by decide)
  have h8 : (ownOff + ownStop) % 8 = 0 := by decide
  refine fragR_append (xs := [_]) (M := RunF s1 l (· = upd M (ownW b ownStop) (BitVec.ofNat 64 code)))
    (fragR_of ?_) (fragR_ret o rfl fun u h => ⟨_, rfl, by rw [h.2]; exact hR⟩)
  exact DN.News.ArticleRun.runF_storeA o (SessionAppend.at_lower (by decide)) rfl (A := b) (y := ownOff + ownStop)
    (hcov.2 _ hst.1 hst.2 h8) (fun u h => by simp only [eval, h.1.base, hb0]; rfl)
    (val := fun _ => BitVec.ofNat 64 code)
    (fun u h => rfl) fun m e => by rw [e]; rfl

/-- The loop's body: an octet of the batch at `X` read, the run stopped unless it is visible. -/
def scanBody (X : Nat) : List Syntax.PStmt :=
  [.dec "cz" (.loadb (Syntax.eAdd (SessionStore.at_ (nextOff + X)) (Syntax.v "ij"))),
   .ite (SessionStore.or2 (Syntax.eLt (Syntax.v "cz") (Syntax.n 33)) (Syntax.eLt (Syntax.n 126) (Syntax.v "cz")))
     (SessionStore.stop badIdentity) [],
   SessionStore.inc "ij"]

theorem visible_toNat (y : DN.News.FrameSpec.Byte) :
    isVisible y = !decide ((y.setWidth 64).toNat < 33 ∨ 126 < (y.setWidth 64).toNat) := by
  have : (y.setWidth 64).toNat = y.toNat := by simp; have := y.isLt; omega
  rw [this]; unfold isVisible
  by_cases h1 : 33 ≤ y.toNat <;> by_cases h2 : y.toNat ≤ 126 <;> simp [h1, h2] <;> omega

/-- **The octets checked**: from `ij` at zero, each of `bs` visible, else the run stopped. -/
theorem scan_frag (o : Oracle σ) {R : Ret} {s1 : PancakeState σ} {b : Word} (hb0 : s1.baseAddr = b)
    (hcov : Analyzer.Covers SessionLayout.size s1.memaddrs b) {L : List (String × Value)} {M : Word → Word}
    {X : Nat} {len : String} {bs : List DN.News.FrameSpec.Byte} (hlen : L.lookup len = some (BitVec.ofNat 64 bs.length))
    (hbl : bs.length < 2 ^ 62) (hbs : Chunk (withMem s1 M) (nextW b X) bs) (hfij : Fresh "ij" L = true)
    (hfcz : Fresh "cz" L = true) (hlij : len ≠ "ij") (hX0 : nextOff + X ≠ 0)
    (hR : (bs.all isVisible = false) → R (BitVec.ofNat 64 badIdentity)
      (upd M (ownW b ownStop) (BitVec.ofNat 64 badIdentity))) :
    FragR o R [.while (Syntax.eLt (Syntax.v "ij") (Syntax.v len)) (scanBody X)]
      (RunF s1 (("ij", BitVec.ofNat 64 0) :: L) (· = M))
      (fun u => RunF s1 (("ij", BitVec.ofNat 64 bs.length) :: L) (· = M) u ∧ bs.all isVisible = true) := by
  let I : Assn σ := fun u => ∃ k, k ≤ bs.length ∧ (bs.take k).all isVisible = true ∧
    RunF s1 (("ij", BitVec.ofNat 64 k) :: L) (· = M) u
  have hlk : ∀ k : Nat, (("ij", BitVec.ofNat 64 k) :: L).lookup len = some (BitVec.ofNat 64 bs.length) := fun k => by
    rw [lookup_cons_ne hlij]; exact hlen
  have hcond : ∀ u k, k ≤ bs.length → RunF s1 (("ij", BitVec.ofNat 64 k) :: L) (· = M) u →
      eval u (.cmp .less (.var "ij") (.var len)) = some (bw (decide (k < bs.length))) := fun u k hk h =>
    DN.News.FramerCode.eval_lt (by omega) (by omega) (vals_lookup h.1.vals (lookup_head _ _ _))
      (vals_lookup h.1.vals (hlk k))
  have hA := SessionAppend.at_lower hX0
  have hS := SessionAppend.at_lower (show ownOff + ownStop ≠ 0 by decide)
  have lowB : LowKK (scanBody X) := fun k => ⟨_, by
    simp [scanBody, Block.lowerK, Lower.lowerStmt1, Lower.lowerStmtsFold, Lower.lowerExp, Syntax.eAdd, Syntax.eLt,
      Syntax.n, Syntax.v, SessionStore.or2, SessionStore.stop, SessionStore.inc, hA, hS]
    rfl⟩
  refine fragR_conseq (DN.News.ArticleRun.fragR_while o rfl lowB (I := I)
    (fun u k ⟨j, h1, h2, h⟩ => ⟨j, h1, h2, runF_clock _ _ _ u k h⟩)
    (fun u z w ⟨j, h1, h2, h⟩ hz => by
      have hz' : z = "cz" := by simpa [scanBody, declared, SessionStore.stop, SessionStore.inc] using hz
      subst hz'
      exact ⟨j, h1, h2, runF_restore h (fresh_cons (by decide) hfcz) w⟩)
    (fun u ⟨j, h1, _, h⟩ => ⟨_, hcond u j h1 h⟩) ?_)
    (fun u h => ⟨0, Nat.zero_le _, by simp, h⟩) fun u ⟨⟨k, hk, hv, h⟩, h0⟩ => ?_
  · refine fragR_conseq (P0 := fun u => ∃ k, (k < bs.length ∧ (bs.take k).all isVisible = true) ∧
      RunF s1 (("ij", BitVec.ofNat 64 k) :: L) (· = M) u) (fragR_exists lowB fun k => ?_)
      (fun u ⟨⟨k, h1, h2, h⟩, hne⟩ => ⟨k, ⟨by
        rw [hcond u k h1 h] at hne; exact of_decide_eq_true (DN.News.FramerCode.bw_ne0 hne), h2⟩, h⟩) fun _ h => h
    refine fragR_pure _ (fun u h => h.1) lowB fun ⟨hk, hv⟩ =>
      fragR_conseq (P0 := RunF s1 (("ij", BitVec.ofNat 64 k) :: L) (· = M)) ?_ (fun u h => h.2) fun _ h => h
    let y := bs[k]
    let L1 : List (String × Value) := ("cz", y.setWidth 64) :: ("ij", BitVec.ofNat 64 k) :: L
    have hfz : Fresh "cz" (("ij", BitVec.ofNat 64 k) :: L) = true := fresh_cons (by decide) hfcz
    have hld : Lower.lowerExp (.loadb (Syntax.eAdd (SessionStore.at_ (nextOff + X)) (Syntax.v "ij"))) =
        some (.loadByte (.op .add (.op .add .base (.const (BitVec.ofNat 64 (nextOff + X)))) (.var "ij"))) := by
      simp [Lower.lowerExp, Syntax.eAdd, Syntax.v, hA]
    refine fragR_append (xs := [_]) (fragR_of (runF_dec o hld hfz (v := y.setWidth 64) fun u h => ?_)) ?_
    · have hij : u.locals "ij" = some (BitVec.ofNat 64 k) := vals_lookup h.1.vals (lookup_head _ _ _)
      have hb := hbs k hk
      simp only [withMem] at hb
      simp only [eval, h.1.base, hb0, hij, h.2, h.1.memaddrs, h.1.be]
      rw [show b + BitVec.ofNat 64 (nextOff + X) + BitVec.ofNat 64 k = nextW b X + BitVec.ofNat 64 k from rfl, hb]
    refine fragR_append (xs := [_]) (M := fun u => RunF s1 L1 (· = M) u ∧ isVisible y = true) ?_ ?_
    · have lowStop : LowKK (SessionStore.stop badIdentity) := fun k => ⟨_, by
        simp [SessionStore.stop, Block.lowerK, Lower.lowerStmt1, Lower.lowerExp, Syntax.n, hS]
        rfl⟩
      refine fragR_if o rfl lowStop (fun k => ⟨k, rfl⟩)
        (fun u k h => ⟨runF_clock _ _ _ u k h.1, h.2⟩) (fun _ _ _ _ hy => nomatch hy) (fun _ _ _ _ hy => nomatch hy)
        (b := !isVisible y) (fun u h => by
          refine (out_eval (lo := 33) (hi := 126)
            (DN.News.FramerCode.ev_var (vals_lookup h.1.vals (lookup_head _ _ _))) (by decide) (by decide)).trans ?_
          rw [visible_toNat, Bool.not_not]
          rfl) (fun hb => ?_) fun hb => fragR_of (frag_nil o fun u h => ⟨h, by simpa using hb⟩)
      refine stop_frag o hb0 hcov (hR ?_)
      have hy : isVisible y = false := by simpa using hb
      rw [Bool.eq_false_iff]
      intro hall
      have := List.all_eq_true.1 hall y (List.getElem_mem hk)
      rw [hy] at this
      exact absurd this (by decide)
    · refine fragR_pure _ (fun u h => h.2) (lowK_any _ (k := .skip) rfl) fun hy => fragR_conseq
        (fragR_of (runF_set o rfl (x := "ij") (w := BitVec.ofNat 64 k) (by
          rw [lookup_cons_ne (by decide)]; exact lookup_head _ _ _) (v := BitVec.ofNat 64 (k + 1))
          fun u h => DN.News.AbnfComment.ev_inc (vals_lookup h.1.vals (by
            rw [lookup_cons_ne (by decide)]; exact lookup_head _ _ _)))) (fun u h => h.1) fun u h => ?_
      refine ⟨k + 1, hk, ?_, runF_mono h (fun q hq => ?_) fun _ e => e⟩
      · rw [List.take_add_one, List.getElem?_eq_getElem hk]
        simp only [Option.toList_some, List.all_append, hv, Bool.true_and]
        simpa using hy
      · rcases List.mem_cons.1 hq with rfl | hq
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (DN.News.FunRun.mem_without
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq)) (DN.News.ScanRun.fresh_ne hfij q hq))
  · rw [hcond u k hk h] at h0
    have hkl : k = bs.length := by
      have := DN.News.FramerCode.bw_eq0 h0; simp at this; omega
    subst hkl
    rw [List.take_length] at hv
    exact ⟨h, hv⟩

/-- What a copy of identity octets leaves. The locals are kept but `ik`, past the octets, which lie at `D`. Every other
octet, and every word outside theirs, is as it was. -/
def Copied (s1 : PancakeState σ) (L : List (String × Value)) (D : Word) (bs : List DN.News.FrameSpec.Byte)
    (M : Word → Word) (u : PancakeState σ) : Prop :=
  ∃ M', RunF s1 (("ik", BitVec.ofNat 64 bs.length) :: without "ik" L) (· = M') u ∧
    Chunk (withMem s1 M') D bs ∧
    (∀ a, (∀ i, i < bs.length → a ≠ D + BitVec.ofNat 64 i) →
      memLoadByte M' s1.memaddrs s1.be a = memLoadByte M s1.memaddrs s1.be a) ∧
    ∀ w, (∀ i, i < bs.length → w ≠ byteAlign (D + BitVec.ofNat 64 i)) → M' w = M w

/-- **Identity octets copied** from the batch at `XS` to the session's own words at `XD`. -/
theorem copyId_frag (o : Oracle σ) {s1 : PancakeState σ} {b : Word} (hb0 : s1.baseAddr = b)
    (hcov : Analyzer.Covers SessionLayout.size s1.memaddrs b) {L : List (String × Value)} {M : Word → Word}
    {XD XS : Nat} {len : String} {bs : List DN.News.FrameSpec.Byte} (hXD : XD + bs.length ≤ ownTexts)
    (hXS : XS + bs.length ≤ nextLen) (hXS0 : XS < nextLen) (hik : ∃ v, L.lookup "ik" = some v)
    (hlen : L.lookup len = some (BitVec.ofNat 64 bs.length)) (hlk : len ≠ "ik")
    (hbs : Chunk (withMem s1 M) (nextW b XS) bs) :
    Frag o (SessionStore.copy "ik" (SessionStore.at_ (ownOff + XD)) (SessionStore.at_ (nextOff + XS)) (Syntax.v len))
      (RunF s1 L (· = M)) (Copied s1 L (ownW b XD) bs M) := by
  have hnx := SessionHost.next_in (x := XS) hXS0
  obtain ⟨hno, hot, ht62⟩ := own_facts
  have hS : SessionLayout.size < 2 ^ 63 := SessionAppend.size_lt
  have h64 : 64 ≤ ownOff := by decide
  have hfl : Analyzer.floor = 64 := rfl
  have hd := SessionAppend.at_lower (X := ownOff + XD) (by omega)
  have hs := SessionAppend.at_lower (X := nextOff + XS) (by omega)
  intro k R Q _ hk
  refine ⟨_, SessionAppend.copy_lowerK hd hs rfl k, SessionAppend.copy_then o (fun s h => ?_) hk⟩
  have hbase : s.baseAddr = b := h.1.base.trans hb0
  have hbl : bs.length < 2 ^ 62 := by omega
  refine ⟨b + BitVec.ofNat 64 (ownOff + XD), b + BitVec.ofNat 64 (nextOff + XS), bs,
    ⟨?_, by simp only [eval, hbase], by simp only [eval, hbase], vals_lookup h.1.vals hlen, hbl, ?_, ?_, ?_,
      ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩, trivial⟩,
      ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩, hlk⟩⟩, ?_⟩
  · obtain ⟨v, hv⟩ := hik; exact ⟨v, vals_lookup h.1.vals hv⟩
  · intro i hi
    rw [getElem!_pos bs i hi, h.2, h.1.memaddrs, h.1.be]
    exact hbs i hi
  · intro i hi
    rw [h.1.memaddrs]
    exact SessionHost.byte_dom hcov (x := ownOff + XD) (by have : Analyzer.floor = 64 := rfl; omega) i (by omega)
  · intro i i' hi hi'
    rw [Bytes.add_ofNat, Bytes.add_ofNat]
    exact DN.News.ScanRun.at_ne (A := b) (by omega) (by omega) (by omega)
  · intro u ⟨hK, hj, hD, hb', hw⟩
    refine ⟨u.memory, ⟨⟨fun q hq => ?_, hK.memaddrs.trans h.1.memaddrs, hK.base.trans h.1.base,
      hK.code.trans h.1.code, hK.be.trans h.1.be⟩, rfl⟩, ?_, ?_, ?_⟩
    · rcases List.mem_cons.1 hq with rfl | hq
      · exact hj
      · have hne : q.1 ≠ "ik" := by simpa [without] using (List.mem_filter.1 hq).2
        rw [hK.locals _ hne]; exact h.1.vals q (List.mem_filter.1 hq).1
    · intro i hi
      have := hD i hi
      rw [getElem!_pos bs i hi, hK.memaddrs, hK.be, h.1.memaddrs, h.1.be] at this
      exact this
    · intro a ha
      have := hb' a ha
      rw [hK.memaddrs, hK.be, h.1.memaddrs, h.1.be, h.2] at this
      exact this
    · intro w hw'
      rw [hw w hw', h.2]

/-! ## Places -/

/-- The own words `identityTake` reads and writes, by number. -/
theorem id_nums :
    ownReady = 8 ∧ ownStop = 16 ∧ ownRevLen = 24 ∧ ownRev = 32 ∧ ownSrcLen = 96 ∧ ownSrc = 104 ∧
    revMax = 64 ∧ srcMax = 200 ∧ ownOff % 8 = 0 ∧ 304 ≤ ownTexts := by decide

/-- A word copied into at `XD`, within the identity's own words, is one `identityTake` writes. -/
theorem copied_took {b : Word} (hb : b.toNat % 8 = 0) {y XD n i : Nat} (hy : y < 2 ^ 64) (hT : ¬Took y)
    (hlo : ownRev ≤ XD) (hhi : XD + n ≤ ownSrc + srcMax) (hX8 : XD % 8 = 0) (hi : i < n) :
    b + BitVec.ofNat 64 y ≠ byteAlign (ownW b XD + BitVec.ofNat 64 i) := by
  obtain ⟨-, -, h3, h4, -, h6, -, h8, h9, h10⟩ := id_nums
  have hS : SessionLayout.size < 2 ^ 63 := SessionAppend.size_lt
  have ho := own_facts.2.1
  rw [ownW, Bytes.add_ofNat, show b + BitVec.ofNat 64 (ownOff + XD + i) = at_ b (ownOff + XD + i) from rfl,
    DN.News.ScanRun.align_at hb]
  have hle : (ownOff + XD + i) / 8 * 8 ≤ ownOff + XD + i := Nat.div_mul_le_self _ _
  have hge : ownOff + XD ≤ (ownOff + XD + i) / 8 * 8 := by omega
  refine DN.News.ScanRun.at_ne (A := b) hy (by omega) fun e => hT (.inr ⟨by omega, by omega⟩)

/-- Word `k` of the own words, one `identityTake` writes, is not `y`, one it does not. -/
theorem own_took {b : Word} {y k : Nat} (hy : y < 2 ^ 64) (hT : ¬Took y) (hk : Took (ownOff + k))
    (hk2 : ownOff + k < 2 ^ 64) : b + BitVec.ofNat 64 y ≠ ownW b k :=
  DN.News.ScanRun.at_ne (A := b) hy hk2 fun e => hT (e ▸ hk)

/-! ## `identityTake` -/

/-- The words the body ends with: the identity held kept, or the batch's taken in. -/
def Done0 (b : Word) (s1 : PancakeState σ) : Assn σ := fun u => ∃ M', RunF s1 [] (· = M') u ∧ Kept0 b s1 M'

theorem done0_clock (b : Word) (s1 : PancakeState σ) : Safe.ClockFree (Done0 b s1) :=
  fun u k ⟨M', h, hk⟩ => ⟨M', runF_clock _ _ _ u k h, hk⟩

theorem done0_restore {b : Word} {s1 u : PancakeState σ} (h : Done0 b s1 u) (y : String) (v : Option Value) :
    Done0 b s1 (restore u y v) :=
  let ⟨M', hr, hk⟩ := h
  ⟨M', runF_restore hr rfl v, hk⟩

/-- The identity's octets taken in, the batch's checked first. -/
theorem take_frag (o : Oracle σ) {s1 : PancakeState σ} {b : Word} (hb0 : s1.baseAddr = b) (hb : b.toNat % 8 = 0)
    (hcov : Analyzer.Covers SessionLayout.size s1.memaddrs b) (hr0 : s1.memory (ownW b ownReady) = 0)
    {xs : List Syntax.PStmt} (hxs : xs = match Session.identity with
      | [.ite _ t _] => t
      | _ => []) :
    FragR o (IdRet b s1) xs (RunF s1 [] (· = s1.memory)) (Done0 b s1) := by
  subst hxs
  simp only [Session.identity]
  have hn := fun x (h : x < nextLen) => SessionHost.next_in h
  have hf : Analyzer.floor = 64 := rfl
  let M0 := s1.memory
  let RW := M0 (nextW b nextRevLen)
  let SW := M0 (nextW b nextSrcLen)
  let RL := RW.toNat
  let SL := SW.toNat
  let L1 : List (String × Value) := [("rvl", RW)]
  let L2 : List (String × Value) := ("scl", SW) :: L1
  have hrl : Lower.lowerExp (SessionStore.ld (SessionStore.at_ (nextOff + nextRevLen))) =
      some (.loadWord (.op .add .base (.const (BitVec.ofNat 64 (nextOff + nextRevLen))))) := by
    simp [SessionStore.ld, Lower.lowerExp, SessionAppend.at_lower (show nextOff + nextRevLen ≠ 0 by decide)]
  have hsl : Lower.lowerExp (SessionStore.ld (SessionStore.at_ (nextOff + nextSrcLen))) =
      some (.loadWord (.op .add .base (.const (BitVec.ofNat 64 (nextOff + nextSrcLen))))) := by
    simp [SessionStore.ld, Lower.lowerExp, SessionAppend.at_lower (show nextOff + nextSrcLen ≠ 0 by decide)]
  have h1 := hn nextRevLen (by decide)
  have h2 := hn nextSrcLen (by decide)
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o hrl rfl (v := RW) fun u h =>
    ld_eval hb0 hcov h (by decide) (by omega) h1.2)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o hsl rfl (v := SW) fun u h =>
    ld_eval hb0 hcov h (by decide) (by omega) h2.2)) ?_
  -- the lengths checked
  have hbad :
      ∀ i, NextIdentity b i s1 → ¬(1 ≤ RL ∧ RL ≤ revMax ∧ 1 ≤ SL ∧ SL ≤ srcMax) → i.ok = false :=
    fun i hi hn' => ok_lengths (by rw [← hi.1, ← hi.2.1]; exact hn')
  refine fragR_append (xs := [_]) (M := fun u => RunF s1 L2 (· = M0) u ∧
    (1 ≤ RL ∧ RL ≤ revMax ∧ 1 ≤ SL ∧ SL ≤ srcMax)) ?_ ?_
  · have hS := SessionAppend.at_lower (show ownOff + ownStop ≠ 0 by decide)
    have lowStop : LowKK (SessionStore.stop badIdentity) := fun k => ⟨_, by
      simp [SessionStore.stop, Block.lowerK, Lower.lowerStmt1, Lower.lowerExp, Syntax.n, hS]
      rfl⟩
    refine fragR_if o rfl lowStop (fun k => ⟨k, rfl⟩)
      (fun u k h => ⟨runF_clock _ _ _ u k h.1, h.2⟩) (fun _ _ _ _ hy => nomatch hy) (fun _ _ _ _ hy => nomatch hy)
      (b := decide (RL < 1 ∨ revMax < RL) || decide (SL < 1 ∨ srcMax < SL)) (fun u h => ?_) (fun hb => ?_)
      fun hb => fragR_of (frag_nil o fun u h => ⟨h, ?_⟩)
    · refine (DN.News.FramerCode.eval_or2
        (out_eval (lo := 1) (hi := revMax) (DN.News.FramerCode.ev_var (vals_lookup h.1.vals
          (show L2.lookup "rvl" = some RW from rfl))) (by decide) (by decide))
        (out_eval (lo := 1) (hi := srcMax) (DN.News.FramerCode.ev_var (vals_lookup h.1.vals
          (show L2.lookup "scl" = some SW from rfl))) (by decide) (by decide))).trans ?_
      rfl
    · refine stop_frag o hb0 hcov (.inr ⟨rfl, rfl, hr0, fun i hi => hbad i hi fun h => ?_⟩)
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hb
      omega
    · simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hb
      omega
  refine fragR_pure _ (fun u h => h.2) (lowK_any _ (k := .skip) rfl) fun hbd => fragR_conseq ?_ (fun u h => h.1)
    fun _ h => h
  have er : revMax = 64 := rfl
  have es : srcMax = 200 := rfl
  obtain ⟨i, hi⟩ := next_identity hcov (s := s1) (b := b)
  have hrv : i.revision.length = RL := hi.1.symm
  have hsc : i.source.length = SL := hi.2.1.symm
  have hcr : Chunk (withMem s1 M0) (nextW b nextRev) i.revision := hi.2.2.1 (by omega)
  have hcs : Chunk (withMem s1 M0) (nextW b nextSrc) i.source := hi.2.2.2 (by omega)
  have hRW : RW = BitVec.ofNat 64 i.revision.length := by rw [hrv]; exact (ofNat_toNat RW).symm
  have hSW : SW = BitVec.ofNat 64 i.source.length := by rw [hsc]; exact (ofNat_toNat SW).symm
  have hsame : ∀ i', NextIdentity b i' s1 → i' = i := fun i' hi' => next_unique hi hi' (by omega) (by omega)
  -- whether each octet is visible
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl (x := "ij") rfl (v := BitVec.ofNat 64 0)
    fun _ _ => rfl)) ?_
  refine fragR_append (xs := [_]) (scan_frag o hb0 hcov (L := L2) (X := nextRev) (len := "rvl") (bs := i.revision)
    (by show some RW = _; rw [hRW]) (by omega) hcr rfl rfl (by decide) (by decide)
    fun hv => .inr ⟨rfl, rfl, hr0, fun i' hi' => by rw [hsame i' hi']; exact ok_rev hv⟩) ?_
  refine fragR_pure _ (fun u h => h.2) (lowK_any _ (k := .skip) rfl) fun hvr => fragR_conseq ?_ (fun u h => h.1)
    fun _ h => h
  refine fragR_append (xs := [_]) (fragR_of (frag_conseq (runF_set o rfl (x := "ij") (lookup_head _ _ _)
    (v := BitVec.ofNat 64 0) fun _ _ => rfl) (fun _ h => h)
    fun u h => by
      rw [show without "ij" (("ij", BitVec.ofNat 64 i.revision.length) :: L2) = L2 from rfl] at h; exact h)) ?_
  refine fragR_append (xs := [_]) (scan_frag o hb0 hcov (L := L2) (X := nextSrc) (len := "scl") (bs := i.source)
    (by show some SW = _; rw [hSW]) (by omega) hcs rfl rfl (by decide) (by decide)
    fun hv => .inr ⟨rfl, rfl, hr0, fun i' hi' => by rw [hsame i' hi']; exact ok_src hv⟩) ?_
  refine fragR_pure _ (fun u h => h.2) (lowK_any _ (k := .skip) rfl) fun hvs => fragR_conseq ?_ (fun u h => h.1)
    fun _ h => h
  let L3 : List (String × Value) := ("ij", BitVec.ofNat 64 i.source.length) :: L2
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl (x := "ik") (l := L3) rfl (v := BitVec.ofNat 64 0)
    fun _ _ => rfl)) ?_
  obtain ⟨n8, n16, n24, n32, n96, n104, n64, n200, no8, n304⟩ := id_nums
  obtain ⟨hno, hot, -⟩ := own_facts
  have hS : SessionLayout.size < 2 ^ 63 := SessionAppend.size_lt
  have hnl : nextSrc + srcMax ≤ nextLen := by decide
  have hnr : nextRev + revMax ≤ nextLen := by decide
  let L4 : List (String × Value) := ("ik", BitVec.ofNat 64 0) :: L3
  -- the revision copied
  refine fragR_append (xs := [_, _]) (fragR_of (copyId_frag o hb0 hcov (L := L4) (XD := ownRev) (XS := nextRev)
    (len := "rvl") (bs := i.revision) (by omega) (by omega) (by omega) ⟨_, rfl⟩ (by show some RW = _; rw [hRW])
    (by decide) hcr)) ?_
  refine fragR_exists (lowK_any _ (k := .skip) rfl) fun M1 => fragR_pure _ (fun u h => h.2)
    (lowK_any _ (k := .skip) rfl) fun ⟨hc1, hb1, hw1⟩ => fragR_conseq ?_ (fun u h => h.1) fun _ h => h
  let L5 : List (String × Value) := ("ik", BitVec.ofNat 64 i.revision.length) :: without "ik" L4
  have hcs1 : Chunk (withMem s1 M1) (nextW b nextSrc) i.source := fun j hj => by
    show memLoadByte M1 s1.memaddrs s1.be _ = _
    rw [hb1 _ fun i' hi' => by
      rw [nextW, Bytes.add_ofNat, ownW, Bytes.add_ofNat]
      exact DN.News.ScanRun.at_ne (A := b) (by omega) (by omega) (by omega)]
    exact hcs j hj
  -- the source copied
  refine fragR_append (xs := [_, _]) (fragR_of (copyId_frag o hb0 hcov (L := L5) (XD := ownSrc) (XS := nextSrc)
    (len := "scl") (bs := i.source) (by omega) (by omega) (by omega) ⟨_, rfl⟩ (by show some SW = _; rw [hSW])
    (by decide) hcs1)) ?_
  refine fragR_exists (lowK_any _ (k := .skip) rfl) fun M2 => fragR_pure _ (fun u h => h.2)
    (lowK_any _ (k := .skip) rfl) fun ⟨hc2, hb2, hw2⟩ => fragR_conseq ?_ (fun u h => h.1) fun _ h => h
  let L6 : List (String × Value) := ("ik", BitVec.ofNat 64 i.source.length) :: without "ik" L5
  -- the lengths and the flag stored
  have st : ∀ (k : Nat) (e : Syntax.PExpr) (E : PancakeExp), Lower.lowerExp e = some E → k < ownTexts →
      k % 8 = 0 → ∀ (val : Word) (M : Word → Word), (∀ u, RunF s1 L6 (· = M) u → eval u E = some val) →
      Frag o [.store (SessionStore.at_ (ownOff + k)) e] (RunF s1 L6 (· = M))
        (RunF s1 L6 (· = upd M (ownW b k) val)) := fun k e E he hk hk8 val M hv => by
    have hx := own_in hk
    exact DN.News.ArticleRun.runF_storeA o (SessionAppend.at_lower (by omega)) he (A := b) (y := ownOff + k)
      (hcov.2 _ (by have : Analyzer.floor = 64 := rfl; omega) hx.2 (by omega))
      (fun u h => by simp only [eval, h.1.base, hb0]; rfl) (val := fun _ => val) hv fun m e => by rw [e]; rfl
  refine fragR_append (xs := [_]) (fragR_of (st ownRevLen _ _ rfl (by omega) (by omega) RW M2 fun u h =>
    DN.News.FramerCode.ev_var (vals_lookup h.1.vals (show L6.lookup "rvl" = some RW from rfl)))) ?_
  refine fragR_append (xs := [_]) (fragR_of (st ownSrcLen _ _ rfl (by omega) (by omega) SW _ fun u h =>
    DN.News.FramerCode.ev_var (vals_lookup h.1.vals (show L6.lookup "scl" = some SW from rfl)))) ?_
  refine fragR_of (frag_conseq (st ownReady (Syntax.n 1) _ rfl (by omega) (by omega) 1 _ fun _ _ => rfl)
    (fun _ h => h) fun u h => ⟨_, runF_mono h (fun _ hq => nomatch hq) fun _ e => e, ?_⟩)
  -- what is left
  have tk : ∀ k, (k = ownReady ∨ k = ownRevLen ∨ k = ownSrcLen) → Took (ownOff + k) := fun k hk => by
    rcases hk with rfl | rfl | rfl
    · exact .inl rfl
    · exact .inr ⟨by omega, by omega⟩
    · exact .inr ⟨by omega, by omega⟩
  have wne : ∀ x y, x < 2 ^ 64 → y < 2 ^ 64 → x ≠ y → b + BitVec.ofNat 64 x ≠ b + BitVec.ofNat 64 y :=
    fun x y hx hy h => DN.News.ScanRun.at_ne (A := b) hx hy h
  have stores : ∀ w, w ≠ ownW b ownRevLen → w ≠ ownW b ownSrcLen → w ≠ ownW b ownReady →
      upd (upd (upd M2 (ownW b ownRevLen) RW) (ownW b ownSrcLen) SW) (ownW b ownReady) 1 w = M2 w :=
    fun w h1 h2 h3 => by rw [upd_ne _ h3, upd_ne _ h2, upd_ne _ h1]
  refine ⟨fun y hy hT => ?_, .inr ⟨hr0, i, hi, ?_⟩⟩
  · refine (stores _ (own_took hy hT (tk _ (.inr (.inl rfl))) (by omega))
      (own_took hy hT (tk _ (.inr (.inr rfl))) (by omega)) (own_took hy hT (tk _ (.inl rfl)) (by omega))).trans ?_
    rw [hw2 _ fun i' hi' => copied_took hb hy hT (by omega) (by omega) (by omega) hi',
      hw1 _ fun i' hi' => copied_took hb hy hT (by omega) (by omega) (by omega) hi']
  · -- an octet of the copies: no word stored holds it
    have keep3 : ∀ x, byteAlign x ≠ ownW b ownRevLen → byteAlign x ≠ ownW b ownSrcLen →
        byteAlign x ≠ ownW b ownReady →
        memLoadByte (upd (upd (upd M2 (ownW b ownRevLen) RW) (ownW b ownSrcLen) SW) (ownW b ownReady) 1)
          s1.memaddrs s1.be x = memLoadByte M2 s1.memaddrs s1.be x := fun x h1 h2 h3 => by
      rw [show upd (upd (upd M2 (ownW b ownRevLen) RW) (ownW b ownSrcLen) SW) (ownW b ownReady) 1 =
        fun k => if k = ownW b ownReady then 1 else upd (upd M2 (ownW b ownRevLen) RW) (ownW b ownSrcLen) SW k
        from rfl, Bytes.load_word_ne h3]
      rw [show upd (upd M2 (ownW b ownRevLen) RW) (ownW b ownSrcLen) SW =
        fun k => if k = ownW b ownSrcLen then SW else upd M2 (ownW b ownRevLen) RW k from rfl,
        Bytes.load_word_ne h2]
      exact Bytes.load_word_ne h1
    have hk3 : ∀ X j, (X = ownRev ∧ j < revMax) ∨ (X = ownSrc ∧ j < srcMax) →
        byteAlign (ownW b X + BitVec.ofNat 64 j) ≠ ownW b ownRevLen ∧
        byteAlign (ownW b X + BitVec.ofNat 64 j) ≠ ownW b ownSrcLen ∧
        byteAlign (ownW b X + BitVec.ofNat 64 j) ≠ ownW b ownReady := fun X j hX => by
      rw [ownW, Bytes.add_ofNat, show b + BitVec.ofNat 64 (ownOff + X + j) = at_ b (ownOff + X + j) from rfl,
        DN.News.ScanRun.align_at hb]
      have hle : (ownOff + X + j) / 8 * 8 ≤ ownOff + X + j := Nat.div_mul_le_self _ _
      have hge : ownOff + X ≤ (ownOff + X + j) / 8 * 8 := by rcases hX with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> omega
      have hx : ownOff + X + j < ownOff + ownSrc + srcMax := by rcases hX with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
      have hn : ∀ k, k = ownRevLen ∨ k = ownSrcLen ∨ k = ownReady → (ownOff + X + j) / 8 * 8 ≠ ownOff + k :=
        fun k hk => by rcases hX with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> rcases hk with rfl | rfl | rfl <;> omega
      exact ⟨wne _ _ (by omega) (by omega) (hn _ (.inl rfl)), wne _ _ (by omega) (by omega) (hn _ (.inr (.inl rfl))),
        wne _ _ (by omega) (by omega) (hn _ (.inr (.inr rfl)))⟩
    have r1 : ownW b ownRevLen ≠ ownW b ownReady := wne _ _ (by omega) (by omega) (by omega)
    have r2 : ownW b ownRevLen ≠ ownW b ownSrcLen := wne _ _ (by omega) (by omega) (by omega)
    have r3 : ownW b ownSrcLen ≠ ownW b ownReady := wne _ _ (by omega) (by omega) (by omega)
    refine ⟨by simp only [withMem]; exact upd_eq _ _ _, ok_of (by omega) hvr hvs, ⟨?_, by omega⟩, ?_,
      ⟨?_, by omega⟩, ?_⟩
    · simp only [withMem]
      rw [upd_ne _ r1, upd_ne _ r2, upd_eq, hRW]
    · intro j hj
      simp only [withMem]
      obtain ⟨e1, e2, e3⟩ := hk3 ownRev j (.inl ⟨rfl, by omega⟩)
      rw [keep3 _ e1 e2 e3, hb2 _ fun i' hi' => by
        rw [ownW, Bytes.add_ofNat, ownW, Bytes.add_ofNat]
        exact wne _ _ (by omega) (by omega) (by omega)]
      exact hc1 j hj
    · simp only [withMem]
      rw [upd_ne _ r3, upd_eq, hSW]
    · intro j hj
      simp only [withMem]
      obtain ⟨e1, e2, e3⟩ := hk3 ownSrc j (.inr ⟨rfl, by omega⟩)
      rw [keep3 _ e1 e2 e3]
      exact hc2 j hj

/-- **`identityTake` takes the batch's identity in, or keeps the one held.** -/
theorem identity_frag (o : Oracle σ) {s1 : PancakeState σ} {b : Word} (hb0 : s1.baseAddr = b)
    (hb : b.toNat % 8 = 0) (hcov : Analyzer.Covers SessionLayout.size s1.memaddrs b) :
    FragR o (IdRet b s1) Session.identity (RunF s1 [] (· = s1.memory)) (Done0 b s1) := by
  have hX := own_in (x := ownReady) (by decide)
  have hr8 : (ownOff + ownReady) % 8 = 0 := by decide
  refine fragR_if o (by simp [Syntax.eEq, Syntax.n, SessionStore.ld, Lower.lowerExp,
      SessionAppend.at_lower (show ownOff + ownReady ≠ 0 by decide)]; rfl)
    (lowK_any _ (k := .skip) rfl) (fun k => ⟨k, rfl⟩) (done0_clock b s1) (fun u y v h _ => done0_restore h y v)
    (fun u y v h _ => done0_restore h y v) (b := decide (s1.memory (ownW b ownReady) = 0)) (fun u h => ?_)
    (fun ht => take_frag o hb0 hb hcov (of_decide_eq_true ht) rfl)
    fun hf => fragR_of (frag_nil o fun u h => ⟨_, h, fun _ _ _ => rfl, .inl ⟨of_decide_eq_false hf, rfl⟩⟩)
  have hl := ld_eval hb0 hcov h hr8 (by omega) hX.2
  have he : eval u (.cmp .equal (.loadWord (.op .add .base (.const (BitVec.ofNat 64 (ownOff + ownReady)))))
      (.const 0)) = some (if s1.memory (ownW b ownReady) = 0 then 1 else 0) := by
    simp only [eval] at hl ⊢
    rw [hl]
    rfl
  refine he.trans ?_
  by_cases h0 : s1.memory (ownW b ownReady) = 0 <;> simp [h0]

/-- **`identityTake`, called**, gives zero: the identity held is kept, or the batch's taken in. Else it gives the stop's
code, the batch's identity not fitting. -/
theorem identityTake_ok (o : Oracle σ) {s1 : PancakeState σ} {b : Word} (hb0 : s1.baseAddr = b)
    (hb : b.toNat % 8 = 0) (hcov : Analyzer.Covers SessionLayout.size s1.memaddrs b) :
    ∃ body, Lower.lower Session.identityTake = some body ∧
      SafeR o (fun s => s = s1) body (IdRet b s1) fun _ => False := by
  obtain ⟨body, hl, hs⟩ := body_of (f := Session.identityTake) (P := RunF s1 [] (· = s1.memory))
    (fragR_append (identity_frag o hb0 hb hcov)
      (fragR_ret o rfl fun u ⟨M', h, hk⟩ => ⟨0, rfl, .inl ⟨rfl, by rw [h.2]; exact hk⟩⟩))
  exact ⟨body, hl, fun s e => hs s (entry_run (l := []) (F := (· = s1.memory)) (fun _ hq => nomatch hq) rfl s e)⟩

/-! ## The premises can hold -/

theorem identityTake_witness : ∃ body, Lower.lower Session.identityTake = some body ∧
    SafeR (Oracle.idle (σ := Unit)) (fun s => s = SessionState.zeroState) body (IdRet 0 SessionState.zeroState)
      fun _ => False :=
  identityTake_ok _ rfl rfl SessionHost.zero_covers

/-- A heap holding the identity `a`, `b` in the session's own words. -/
def idMem (a : Word) : Word :=
  if a = BitVec.ofNat 64 1032576 then 1 else if a = BitVec.ofNat 64 1032592 then 1
  else if a = BitVec.ofNat 64 1032600 then 97 else if a = BitVec.ofNat 64 1032664 then 1
  else if a = BitVec.ofNat 64 1032672 then 98 else 0

def idState : PancakeState Unit := { SessionState.zeroState with memory := idMem }

theorem identityAt_witness : IdentityAt 0 ⟨[97], [98]⟩ idState := by
  have h : ownOff = 1032568 := by decide
  refine ⟨?_, by decide, ⟨?_, by decide⟩, fun j hj => ?_, ⟨?_, by decide⟩, fun j hj => ?_⟩
  · simp only [ownW, h]; decide
  · simp only [ownW, h]; decide
  · obtain rfl : j = 0 := by simp at hj; omega
    simp only [ownW, h, List.getElem_singleton]; decide
  · simp only [ownW, h]; decide
  · obtain rfl : j = 0 := by simp at hj; omega
    simp only [ownW, h, List.getElem_singleton]; decide

theorem kept0_witness : Kept0 0 idState idState.memory :=
  ⟨fun _ _ _ => rfl, .inl ⟨by rw [identityAt_witness.1]; decide, rfl⟩⟩

theorem took_witness : Took (ownOff + ownReady) := .inl rfl

theorem nextIdentity_witness : ∃ i, NextIdentity 0 i SessionState.zeroState := next_identity SessionHost.zero_covers

end DN.Server.SessionIdentity
