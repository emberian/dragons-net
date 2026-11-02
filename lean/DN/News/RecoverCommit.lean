-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.RecoverFirst

/-!
# DN.News.RecoverCommit

A commit the journal's scanner read, noted by recovery's step (`RecoverProg.commitRead`) as `RecoverSpec.recordRead`
notes it: counted, and while the index has room, in its slot — its numbers, its Message-ID and the Message-ID's tag
under the configuration's key, each group's place in the configuration and article number — and the first group the
configuration lacks.
-/

namespace DN.News.RecoverArea

open DN.Compiler DN.Compiler.Wp DN.Compiler.Frag DN.Compiler.Bytes DN.News.Journal DN.News.Recovery
open DN.News.RecoverProg
open DN.News.RecoverSpec (RSt)
open DN.News.ScanRun (St Valid at_ at_add at_inj vals_lookup kept_has stepSpec lookup_cons_ne lookup_head vals_setL
  fresh_cons outside_sub kept_false_eq frag_if vals_head)
open DN.News.FramerCode (bw ev_var eval_or eval_shl)

variable {σ : Type}

/-! ## The scanner's area in recovery's -/

/-- The scanner's area's numbers. -/
theorem snums : ScanProg.sSize = 0 ∧ ScanProg.sBase = 8 ∧ ScanProg.sLen = 16 ∧ ScanProg.sPos = 24 ∧
    ScanProg.sKeyed = 32 ∧ ScanProg.sCount = 40 ∧ ScanProg.sStatus = 48 ∧ ScanProg.sWhy = 56 ∧ ScanProg.sWant = 64 ∧
    ScanProg.sType = 72 ∧ ScanProg.sSeq = 80 ∧ ScanProg.sIdAt = 88 ∧ ScanProg.sIdLen = 96 ∧
    ScanProg.sGroupCount = 104 ∧ ScanProg.sHeader = 112 ∧ ScanProg.sFileSize = 120 ∧ ScanProg.sCrc = 128 ∧
    ScanProg.sGroups = 136 ∧ ScanProg.groupSlot = 24 ∧ ScanProg.sWindow = 1928 ∧ ScanProg.windowRoom = 19168 ∧
    ScanProg.windowMax = 17776 ∧ ScanProg.wanted = 1 ∧ ScanProg.record = 2 ∧ ScanProg.clean = 3 ∧ ScanProg.torn = 4 ∧
    ScanProg.corrupt = 5 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl⟩

theorem scan_dom {A : Word} {dm : Word → Bool} (h : RDom A dm) : ScanRun.Dom (at_ A rScan) dm := fun x hx => by
  have hn := nums
  rw [at_at]; exact h _ (by omega)

theorem scan_locals : ∀ y ∈ ScanProg.locals, y ∈ RecoverProg.locals := fun _ hy => List.mem_append_right _ hy

theorem scan_step : ∀ y ∈ ScanProg.locals, y ∈ stepLocals := fun y hy =>
  List.mem_filter.2 ⟨scan_locals y hy, by
    have : "jsc" ∉ ScanProg.locals := by decide
    simp only [bne_iff_ne, ne_eq]; rintro rfl; exact this hy⟩

theorem not_scanW {A : Word} {y : Nat} (hy : y < rScan ∨ rSlots ≤ y) (hy64 : y < 2 ^ 64) :
    ¬ ScanRun.AreaW (at_ A rScan) (at_ A y) := fun ⟨z, hz, e⟩ => by
  have hn := nums
  rw [at_at] at e
  have := at_inj hy64 (by omega) e
  omega

/-! ## What the scanner leaves read -/

/-- The scanner's word at `x` read, as the program lowers it. -/
def swE (x : Nat) : PancakeExp :=
  .loadWord (if x = 0 then .var "jsc" else .op .add (.var "jsc") (.const (.ofNat 64 x)))

theorem sw_lower (x : Nat) : Lower.lowerExp (sw x) = some (swE x) := by
  by_cases h : x = 0
  · subst h; rfl
  · simp [sw, Syntax.atOff, swE, Lower.lowerExp, Syntax.eAdd, Syntax.v, Syntax.n, h]

theorem mid_sw {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ} (h : PBase A s0)
    {ws : Nat → Word} {os : List (Nat × Word)} {l : List (String × Value)} {u : PancakeState σ}
    (hu : Mid A cfg J r s0 ws os l u) {x : Nat} (hx : x % 8 = 0) (hxs : x < ScanProg.size) :
    eval u (swE x) = some (u.memory (at_ A (rScan + x))) := by
  obtain ⟨E, hE, hv⟩ := ScanRun.e_loadw (p := "jsc") (at_aligned h.hA (x := rScan) (by decide))
    (scan_dom (by rw [hu.kept.memaddrs]; exact h.dom)) (jsc_kept h hu.kept) hx hxs
  have e : some (swE x) = some E := (sw_lower x).symm.trans hE
  cases e; rw [hv, at_at]

/-- A word of the scanner's a phase noted it stored, read. -/
theorem mid_swOut {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ} (h : PBase A s0)
    {ws : Nat → Word} {os : List (Nat × Word)} {l : List (String × Value)} {u : PancakeState σ}
    (hu : Mid A cfg J r s0 ws os l u) {x : Nat} {v : Word} (hm : (rScan + x, v) ∈ os) (h8 : x % 8 = 0)
    (hxs : x < ScanProg.size) : eval u (swE x) = some v := by
  rw [mid_sw h hu h8 hxs]; have e := hu.outs _ hm; dsimp only at e; rw [e]

/-- Offsets `os` lists, none of them `x`: checked by evaluation. -/
theorem apart_of {x : Nat} {os : List (Nat × Word)} (h : (os.map Prod.fst).all (fun y => decide (y ≠ x)) = true) :
    ∀ q ∈ os, q.1 ≠ x := fun q hq => of_decide_eq_true (List.all_eq_true.1 h q.1 (List.mem_map_of_mem hq))

/-! ## What lowers -/

theorem lowKK_kept {fail : List Syntax.PStmt} (hfl : LowKK fail) (x : String) (hi : Nat) :
    LowKK [ScanProg.kept fail x hi] :=
  lowKK_ite rfl hfl (fun k => ⟨k, rfl⟩)

theorem lowKK_slotHead {fail : List Syntax.PStmt} (hfl : LowKK fail) : LowKK (slotHead fail) := by
  have hk := lowKK_kept hfl
  refine lowKK_append (xs := [_, _, _]) (lowK_any _ (k := .skip) (c := _) rfl) ?_
  refine lowKK_append (xs := [_]) (hk _ _) ?_
  refine lowKK_append (xs := [_]) (lowK_any _ (k := .skip) (c := _) rfl) ?_
  refine lowKK_append (xs := [_]) (hk _ _) ?_
  refine lowKK_append (xs := [_]) (lowK_any _ (k := .skip) (c := _) rfl) ?_
  refine lowKK_append (xs := [_]) (hk _ _) ?_
  exact lowK_any _ (k := .skip) (c := _) rfl

theorem lowKK_groupNote {fail : List Syntax.PStmt} (hfl : LowKK fail) : LowKK (groupNote fail) := by
  have hk := lowKK_kept hfl
  refine lowKK_append (xs := [_, _]) (lowK_any _ (k := .skip) (c := _) rfl) ?_
  refine lowKK_append (xs := [_]) (hk _ _) ?_
  refine lowKK_append (xs := [_]) (lowK_any _ (k := .skip) (c := _) rfl) ?_
  refine lowKK_append (xs := [_]) (hk _ _) ?_
  exact lowK_any _ (k := .skip) (c := _) rfl

/-- What a commit read writes in its slot, past its address. -/
theorem lowKK_groups {fail : List Syntax.PStmt} (hfl : LowKK fail) :
    LowKK [.assign "rg" (ScanProg.lit 0), .while (Syntax.eLt (Syntax.v "rg") (Syntax.v "rgc")) (groupNote fail)] :=
  lowKK_append (xs := [_]) (lowK_any _ (k := .skip) (c := _) rfl) (lowKK_while rfl (lowKK_groupNote hfl))

theorem lowKK_slotNote {fail : List Syntax.PStmt} (hfl : LowKK fail) :
    LowKK (slotHead fail ++ SipProg.sipSrc ++ [.store (Syntax.atOff (Syntax.v "rsl") slotTag) (Syntax.v "r"),
      .assign "rg" (ScanProg.lit 0), .while (Syntax.eLt (Syntax.v "rg") (Syntax.v "rgc")) (groupNote fail)]) :=
  lowKK_append (lowKK_append (lowKK_slotHead hfl) ScanRun.lowKK_sip) (lowKK_append (xs := [_])
    (lowK_any _ (k := .skip) (c := _) rfl) (lowKK_groups hfl))

theorem lowKK_commitRead {fail : List Syntax.PStmt} (hfl : LowKK fail) : LowKK (commitRead fail) :=
  lowKK_append (xs := [_, _]) (lowK_any _ (k := .skip) (c := _) rfl) (lowKK_ite rfl (lowKK_append (xs := [_])
    (lowK_any _ (k := .skip) (c := _) rfl) (lowKK_slotNote hfl)) (fun k => ⟨k, rfl⟩))

/-! ## A record read -/

/-- **A record read**: the window kept, the frame within it, and the record the frame's type and payload make. -/
theorem record_facts {J : Bytes} {st st' : St} {rec : Record} (hv : Valid J st) (h : stepSpec J st = .record rec st') :
    st'.base = st.base ∧ st'.len = st.len ∧ st.base ≤ st.pos ∧
      st.pos + 13 + (ScanRun.payloadOf (J.drop st.pos)).length < st.base + st.len ∧
      13 + (ScanRun.payloadOf (J.drop st.pos)).length < (J.drop st.pos).length ∧
      recordOf spec (ScanRun.typeOf (J.drop st.pos)) (ScanRun.payloadOf (J.drop st.pos)) = some rec := by
  simp only [stepSpec] at h
  split at h
  · cases h
  rename_i h1
  split at h
  · cases h
  rename_i h2
  split at h
  · rename_i r taken rest hnx
    split at h
    · cases h
    · simp only [ScanRun.Out.record.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨-, hr, ht⟩ := ScanRun.next_record_of hnx
      obtain ⟨-, -, ht2, ht3⟩ := ScanRun.next_record hnx
      have hl : 13 + readLE ((J.drop st.pos).take 4) + 1 ≤ (J.drop st.pos).length := by omega
      have hpl := ScanRun.payload_length hl
      have := hv.base
      have := Nat.min_le_left (J.length - st.pos) maxFrame
      have := Nat.min_le_right (J.length - st.pos) maxFrame
      simp only [List.length_drop] at ht2 hl
      refine ⟨rfl, rfl, hv.base, ?_, by rw [hpl, List.length_drop]; omega, hr⟩
      rw [hpl]
      have hm : taken ≤ min (J.length - st.pos) maxFrame := Nat.le_min.mpr ⟨by omega, ht3⟩
      omega
  · cases h
  · cases h

/-! ## The commit's fields, kept -/

open DN.News.ScanRun (CommitAt SlotAt)

/-- The commit's fields read where only words other than the scanner's first thousand octets changed. -/
theorem commitAt_keep {A : Word} {o' : Nat} {pl : Bytes} {c : Commit} {u u' : PancakeState σ}
    (h : CommitAt (at_ A rScan) o' pl c u) (hgc : c.groups.length ≤ ScanProg.groupsMax)
    (hm : ∀ y, y < 1000 → u'.memory (at_ A (rScan + y)) = u.memory (at_ A (rScan + y))) :
    CommitAt (at_ A rScan) o' pl c u' :=
  ScanRun.commitAt_of h hgc fun x _ hx _ => by
    have : ScanProg.sKey = 520 := rfl
    rw [at_at]; exact hm x (by omega)

/-- The fields of a commit the scanner read, by name. -/
theorem commitAt_idAt {A : Word} {o' : Nat} {pl : Bytes} {c : Commit} {u : PancakeState σ}
    (h : CommitAt A o' pl c u) : u.memory (at_ A ScanProg.sIdAt) = .ofNat 64 (o' + 13 + 9) := h.2.1

theorem commitAt_idLen {A : Word} {o' : Nat} {pl : Bytes} {c : Commit} {u : PancakeState σ}
    (h : CommitAt A o' pl c u) : u.memory (at_ A ScanProg.sIdLen) = .ofNat 64 c.messageId.length := h.2.2.1

theorem commitAt_count {A : Word} {o' : Nat} {pl : Bytes} {c : Commit} {u : PancakeState σ}
    (h : CommitAt A o' pl c u) : u.memory (at_ A ScanProg.sGroupCount) = .ofNat 64 c.groups.length := h.2.2.2.1

theorem commitAt_header {A : Word} {o' : Nat} {pl : Bytes} {c : Commit} {u : PancakeState σ}
    (h : CommitAt A o' pl c u) : u.memory (at_ A ScanProg.sHeader) = .ofNat 64 c.headerSize := h.2.2.2.2.2.1

theorem commitAt_fileSize {A : Word} {o' : Nat} {pl : Bytes} {c : Commit} {u : PancakeState σ}
    (h : CommitAt A o' pl c u) : u.memory (at_ A ScanProg.sFileSize) = .ofNat 64 c.fileSize := h.2.2.2.2.2.2.1

theorem commitAt_crc {A : Word} {o' : Nat} {pl : Bytes} {c : Commit} {u : PancakeState σ}
    (h : CommitAt A o' pl c u) : u.memory (at_ A ScanProg.sCrc) = .ofNat 64 c.fileCrc := h.2.2.2.2.2.2.2

/-- What a commit read keeps of the scanner's area: the commit's fields and its payload in the window. -/
def CommitIn (A : Word) (o' : Nat) (pl : Bytes) (c : Commit) (u : PancakeState σ) : Prop :=
  CommitAt (at_ A rScan) o' pl c u ∧ BytesAt A (rScan + ScanProg.sWindow + o' + 13) pl u

theorem CommitIn.at' {A : Word} {o' : Nat} {pl : Bytes} {c : Commit} {u : PancakeState σ} (h : CommitIn A o' pl c u) :
    CommitAt (at_ A rScan) o' pl c u := h.1

theorem CommitIn.payload {A : Word} {o' : Nat} {pl : Bytes} {c : Commit} {u : PancakeState σ}
    (h : CommitIn A o' pl c u) : BytesAt A (rScan + ScanProg.sWindow + o' + 13) pl u := h.2

theorem commitIn_stW {A : Word} (hA : A.toNat % 8 = 0) {o' : Nat} {pl : Bytes} {c : Commit} {u : PancakeState σ}
    (h : CommitIn A o' pl c u) (hgc : c.groups.length ≤ ScanProg.groupsMax)
    (hfit : o' + 13 + pl.length ≤ ScanProg.windowMax) {x : Nat} (hx : x < rScan ∨ rSlots ≤ x) (hx64 : x < 2 ^ 64)
    (v : Word) : CommitIn A o' pl c (stW u A x v) := by
  have hs := snums
  have hn := nums
  exact ⟨commitAt_keep h.1 hgc fun y hy => stW_word hx64 (by omega) (by omega) v,
    bytesAt_stW hA h.2 hx64 (by omega) (fun i hi => by omega) v⟩

/-- A store in the slots keeps a commit read. -/
theorem commitIn_slots {A : Word} (hA : A.toNat % 8 = 0) {o' : Nat} {pl : Bytes} {c : Commit}
    (hgc : c.groups.length ≤ ScanProg.groupsMax) (hfit : o' + 13 + pl.length ≤ ScanProg.windowMax) {x : Nat}
    {u : PancakeState σ} {v : Word} (hx1 : rSlots ≤ x) (hx2 : x < RecoverProg.size) (h : CommitIn A o' pl c u) :
    CommitIn A o' pl c (stW u A x v) := by
  have : RecoverProg.size < 2 ^ 64 := by decide
  exact commitIn_stW hA h hgc hfit (.inr hx1) (by omega) v

theorem commitIn_put {A : Word} (hA : A.toNat % 8 = 0) {o' : Nat} {pl : Bytes} {c : Commit} {u : PancakeState σ}
    (h : CommitIn A o' pl c u) (hgc : c.groups.length ≤ ScanProg.groupsMax)
    (hfit : o' + 13 + pl.length ≤ ScanProg.windowMax) {z : Nat} (hz : z / 8 * 8 < rScan ∨ rSlots ≤ z / 8 * 8)
    (hz64 : z < 2 ^ 63) (b : BitVec 8) : CommitIn A o' pl c { u with memory := putByte u.memory u.be (at_ A z) b } := by
  rw [putByte_stW hA]; exact commitIn_stW hA h hgc hfit hz (by omega) _

/-- What a commit of the store's has. -/
theorem ok_bounds {c : Commit} (h : c.ok = true) : c.seq < 2 ^ 64 ∧ 1 ≤ c.messageId.length ∧
    c.messageId.length ≤ 250 ∧ c.groups.length ≤ ScanProg.groupsMax ∧
    (∀ g ∈ c.groups, 1 ≤ g.name.length ∧ g.name.length ≤ groupNameMax ∧ g.number < 2 ^ 31) ∧
    c.fileSize < 2 ^ 32 ∧ c.fileCrc < 2 ^ 32 ∧ c.headerSize ≤ c.fileSize := by
  simp only [Commit.ok, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, h1⟩, h2⟩, h3⟩, _⟩, h4⟩, h5⟩, _⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h1, h2, h3, h4, fun g hg => ⟨(h5 g hg).1.1.1, (h5 g hg).1.1.2, (h5 g hg).2⟩, h7, h8, h6⟩

/-- The locals a commit read sets. -/
def crNames : List String :=
  ["rcm", "rsl", "rgc", "ril", "rio", "rwp", "rj", "k", "p", "n", "rg", "rgs", "rga", "rgl", "rx", "rc", "rgn", "rcp",
   "rok"] ++ ScanRun.sipNames

theorem cr_step : ∀ y ∈ crNames, y ∈ stepLocals := fun y hy => List.mem_filter.2 ⟨by revert y hy; decide, by
  have : ∀ y ∈ crNames, y ≠ "jsc" := by decide
  simp only [bne_iff_ne, ne_eq]; exact this y hy⟩

theorem slotAt_aligned (i : Nat) : (slotAt i) % 8 = 0 := by
  have hn := nums
  simp only [slotAt, show slotSize = 416 from rfl]; omega

/-- **A word stored where `Rest` reads nothing**, what else holds as the caller says. -/
theorem far_store (o : Oracle σ) {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ}
    (h : PBase A s0) {ws : Nat → Word} {os : List (Nat × Word)} {l : List (String × Value)}
    (hos : ∀ q ∈ os, rScan ≤ q.1 ∧ q.1 < rSlots) {x : Nat} (hx : Far r x) (hx8 : x % 8 = 0) {d e : Syntax.PExpr}
    {D E : PancakeExp} (hd : Lower.lowerExp d = some D) (he : Lower.lowerExp e = some E) {val : Word}
    {F F' : Assn σ} (hF'c : Safe.ClockFree F')
    (hv : ∀ u, Mid A cfg J r s0 ws os l u → F u → eval u D = some (at_ A x) ∧ eval u E = some val)
    (hF : ∀ u, Mid A cfg J r s0 ws os l u → F u → F' (stW u A x val)) :
    Frag o [.store d e] (fun u => Mid A cfg J r s0 ws os l u ∧ F u) (fun u => Mid A cfg J r s0 ws os l u ∧ F' u) := by
  have hb := far_bounds hx
  have e1 : rTorn = 480 := rfl
  have e2 : rScan = 5760 := rfl
  have e3 : rSlots = 26856 := rfl
  have e4 : RecoverProg.size = 1730792 := rfl
  have hxs : x < RecoverProg.size := by omega
  refine store_frag o hd he (fun s k ⟨h1, h2⟩ => ⟨mid_clock s k h1, hF'c s k h2⟩) fun u ⟨hu, hf⟩ =>
    ⟨_, val, (hv u hu hf).1, (hv u hu hf).2, ?_, mid_far h hu hx hx8
      (fun q hq => by have := hos q hq; omega) val, hF u hu hf⟩
  have := h.dom x hxs
  rw [hu.kept.memaddrs]; simp only [at_] at this ⊢
  rwa [byteAlign_of_aligned h.hA (X := x) hx8] at this

/-- **An octet stored where `Rest` reads nothing**. -/
theorem far_storeb (o : Oracle σ) {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ}
    (h : PBase A s0) {ws : Nat → Word} {os : List (Nat × Word)} {l : List (String × Value)}
    (hos : ∀ q ∈ os, rScan ≤ q.1 ∧ q.1 < rSlots) {z : Nat} (hz : Far r (z / 8 * 8)) (hzs : z < RecoverProg.size)
    {d e : Syntax.PExpr} {D E : PancakeExp} (hd : Lower.lowerExp d = some D) (he : Lower.lowerExp e = some E)
    {b : BitVec 8} {F F' : Assn σ} (hF'c : Safe.ClockFree F')
    (hv : ∀ u, Mid A cfg J r s0 ws os l u → F u → eval u D = some (at_ A z) ∧ eval u E = some (b.setWidth 64))
    (hF : ∀ u, Mid A cfg J r s0 ws os l u → F u → F' { u with memory := putByte u.memory u.be (at_ A z) b }) :
    Frag o [.storeb d e] (fun u => Mid A cfg J r s0 ws os l u ∧ F u) (fun u => Mid A cfg J r s0 ws os l u ∧ F' u) := by
  have hb := far_bounds hz
  have e1 : rTorn = 480 := rfl
  have e2 : rScan = 5760 := rfl
  have e3 : rSlots = 26856 := rfl
  refine storeb_frag o hd he (fun s k ⟨h1, h2⟩ => ⟨mid_clock s k h1, hF'c s k h2⟩) fun u ⟨hu, hf⟩ =>
    ⟨_, b.setWidth 64, (hv u hu hf).1, (hv u hu hf).2, by rw [hu.kept.memaddrs]; exact h.dom z hzs, ?_, ?_⟩
  · rw [Bytes.setWidth64_8, putByte_stW h.hA]
    exact mid_far h hu hz (by omega) (fun q hq => by have := hos q hq; omega) _
  · rw [Bytes.setWidth64_8]; exact hF u hu hf

/-- A word of the slot after the commits' stored. -/
theorem slot_store (o : Oracle σ) {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ}
    (h : PBase A s0) (hcap : r.commits.length < capacity) {ws : Nat → Word} {os : List (Nat × Word)}
    {l : List (String × Value)} (hos : ∀ q ∈ os, rScan ≤ q.1 ∧ q.1 < rSlots) {off : Nat} (hoff8 : off % 8 = 0)
    (hoff : off < slotSize) {d e : Syntax.PExpr} {D E : PancakeExp} (hd : Lower.lowerExp d = some D)
    (he : Lower.lowerExp e = some E) {val : Word} {F F' : Assn σ} (hF'c : Safe.ClockFree F')
    (hv : ∀ u, Mid A cfg J r s0 ws os l u → F u →
      eval u D = some (at_ A (slotAt r.commits.length + off)) ∧ eval u E = some val)
    (hF : ∀ u, Mid A cfg J r s0 ws os l u → F u → F' (stW u A (slotAt r.commits.length + off) val)) :
    Frag o [.store d e] (fun u => Mid A cfg J r s0 ws os l u ∧ F u) (fun u => Mid A cfg J r s0 ws os l u ∧ F' u) :=
  far_store o h hos (.inr ⟨by omega, by omega, hcap⟩) (by have := slotAt_aligned r.commits.length; omega) hd he hF'c
    hv hF

/-- An octet of the slot after the commits' stored. -/
theorem slot_storeb (o : Oracle σ) {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ}
    (h : PBase A s0) (hcap : r.commits.length < capacity) {ws : Nat → Word} {os : List (Nat × Word)}
    {l : List (String × Value)} (hos : ∀ q ∈ os, rScan ≤ q.1 ∧ q.1 < rSlots) {off : Nat} (hoff : off < slotSize)
    {d e : Syntax.PExpr} {D E : PancakeExp} (hd : Lower.lowerExp d = some D) (he : Lower.lowerExp e = some E)
    {b : BitVec 8} {F F' : Assn σ} (hF'c : Safe.ClockFree F')
    (hv : ∀ u, Mid A cfg J r s0 ws os l u → F u →
      eval u D = some (at_ A (slotAt r.commits.length + off)) ∧ eval u E = some (b.setWidth 64))
    (hF : ∀ u, Mid A cfg J r s0 ws os l u → F u →
      F' { u with memory := putByte u.memory u.be (at_ A (slotAt r.commits.length + off)) b }) :
    Frag o [.storeb d e] (fun u => Mid A cfg J r s0 ws os l u ∧ F u) (fun u => Mid A cfg J r s0 ws os l u ∧ F' u) := by
  obtain ⟨-, s2⟩ := slotAt_le hcap
  have hal := slotAt_aligned r.commits.length
  exact far_storeb o h hos (.inr ⟨by omega, by omega, hcap⟩) (by omega) hd he hF'c hv hF

/-! ## A group's place in the configuration -/

/-- Where among the configuration's first `k` groups `name` is, the last, else `groupsMax`. -/
def ixUpTo (cfg : Config) (name : Bytes) (k : Nat) : Nat :=
  (List.range k).foldl (fun x c => if cfg.groups.getD c [] = name then c else x) groupsMax

theorem groupIx_eq (cfg : Config) (name : Bytes) :
    groupIx cfg name = ixUpTo cfg name (min cfg.groups.length groupsMax) := rfl

theorem ix_succ (cfg : Config) (name : Bytes) (k : Nat) :
    ixUpTo cfg name (k + 1) = if cfg.groups.getD k [] = name then k else ixUpTo cfg name k := by
  simp only [ixUpTo, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- Where the search ends: nowhere among the first `k`, or at one with the name. -/
theorem ix_spec (cfg : Config) (name : Bytes) : ∀ k, k ≤ groupsMax →
    (ixUpTo cfg name k = groupsMax ∧ ∀ j, j < k → cfg.groups.getD j [] ≠ name) ∨
      (ixUpTo cfg name k < k ∧ cfg.groups.getD (ixUpTo cfg name k) [] = name)
  | 0, _ => .inl ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | k + 1, hk => by
    rw [ix_succ]
    by_cases e : cfg.groups.getD k [] = name
    · rw [if_pos e]; exact .inr ⟨by omega, e⟩
    · rw [if_neg e]
      rcases ix_spec cfg name k (by omega) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact .inl ⟨h1, fun j hj => by
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
          · exact h2 j hj
          · exact e⟩
      · exact .inr ⟨by omega, h2⟩

theorem ix_lt (cfg : Config) (name : Bytes) {k : Nat} (hk : k ≤ groupsMax) : ixUpTo cfg name k ≤ groupsMax := by
  rcases ix_spec cfg name k hk with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega

/-- **Nowhere in the configuration** exactly when the configuration lacks the name. -/
theorem ix_none {cfg : Config} (hc : cfg.groups.length ≤ groupsMax) (name : Bytes) :
    ixUpTo cfg name cfg.groups.length = groupsMax ↔ cfg.groups.contains name = false := by
  have hn := nums
  constructor
  · intro h
    rcases ix_spec cfg name _ hc with ⟨_, h2⟩ | ⟨h1, _⟩
    · rw [Bool.eq_false_iff]; intro hm
      simp only [List.contains_iff_exists_mem_beq, beq_iff_eq] at hm
      obtain ⟨x, hx, rfl⟩ := hm
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
      exact h2 j hj (by simp [List.getD_eq_getElem?_getD, hj])
    · omega
  · intro h
    rcases ix_spec cfg name _ hc with ⟨h1, _⟩ | ⟨h1, h2⟩
    · exact h1
    · exfalso
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1] at h2
      simp only [Option.getD_some] at h2
      have : cfg.groups.contains name = true := by
        rw [List.contains_iff_exists_mem_beq]; exact ⟨_, List.getElem_mem h1, by simp [h2]⟩
      rw [h] at this; cases this

/-! ## The first group the configuration lacks -/

/-- The first of `gs` the configuration lacks. -/
def unkFirst (cfg : Config) (gs : List Group) : Option Bytes :=
  (gs.find? fun g => !cfg.groups.contains g.name).map (·.name)

theorem unkFirst_snoc (cfg : Config) (gs : List Group) (g : Group) :
    unkFirst cfg (gs ++ [g]) = (unkFirst cfg gs <|> if cfg.groups.contains g.name then none else some g.name) := by
  simp only [unkFirst, List.find?_append, List.find?_cons, List.find?_nil]
  cases hf : gs.find? (fun g => !cfg.groups.contains g.name) with
  | some x => simp
  | none => cases cfg.groups.contains g.name <;> simp

/-! ## Two names compared -/

/-- **Two names of a length compared** octet by octet: `rok` set when they are the same. -/
theorem nameCmp_frag (o : Oracle σ) {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ}
    (h : PBase A s0) {ws : Nat → Word} {os : List (Nat × Word)} {l : List (String × Value)}
    (hl : ScanRun.Outside ["rok", "rj"] l = true) {a b : Bytes} (hab : a.length = b.length) (hlen : a.length ≤ 64)
    {pa pw : Word} {vs : List (String × Value)} (hfo : ScanRun.Fresh "rok" vs = true)
    (hfj : ScanRun.Fresh "rj" vs = true) (hrcp : vs.lookup "rcp" = some pa) (hrwp : vs.lookup "rwp" = some pw)
    (hrgl : vs.lookup "rgl" = some (.ofNat 64 a.length))
    {G : Assn σ} (hGc : Safe.ClockFree G) (hGs : ∀ u y v, y ∈ ["rok", "rj"] → G u → G (setL u y v))
    (hA : ∀ u, G u → ∀ j (hj : j < a.length),
      memLoadByte u.memory u.memaddrs u.be (pa + BitVec.ofNat 64 8 + BitVec.ofNat 64 j) = some a[j])
    (hB : ∀ u, G u → ∃ w, u.locals "rga" = some w ∧ ∀ j (hj : j < b.length),
      memLoadByte u.memory u.memaddrs u.be (pw + w + BitVec.ofNat 64 j) = some b[j]) :
    Frag o [.assign "rok" (ScanProg.lit 1), .assign "rj" (ScanProg.lit 0),
      .while (Syntax.eLt (Syntax.v "rj") (Syntax.v "rgl"))
        [.ite (ScanProg.ne (.loadb (Syntax.eAdd (Syntax.atOff (Syntax.v "rcp") 8) (Syntax.v "rj")))
            (.loadb (Syntax.eAdd (Syntax.eAdd (Syntax.v "rwp") (Syntax.v "rga")) (Syntax.v "rj"))))
          [.assign "rok" (ScanProg.lit 0)] [],
         ScanProg.inc "rj"]]
      (fun u => Mid A cfg J r s0 ws os l u ∧ ScanRun.Vals u vs ∧ G u)
      (fun u => Mid A cfg J r s0 ws os l u ∧
        ScanRun.Vals u (("rj", .ofNat 64 a.length) :: ("rok", bw (decide (a = b))) :: vs) ∧ G u) := by
  have hrok : "rok" ∈ stepLocals := by decide
  have hrj : "rj" ∈ stepLocals := by decide
  have hlo : ScanRun.Fresh "rok" l = true := ScanRun.fresh_of_outside hl (by decide)
  have hlj : ScanRun.Fresh "rj" l = true := ScanRun.fresh_of_outside hl (by decide)
  let I (j : Nat) : Assn σ := fun u => Mid A cfg J r s0 ws os l u ∧
    ScanRun.Vals u (("rj", .ofNat 64 j) :: ("rok", bw (decide (a.take j = b.take j))) :: vs) ∧ G u ∧ j ≤ a.length
  have hIc : ∀ j, Safe.ClockFree (I j) := fun _ s k ⟨h1, h2, h3, h4⟩ => ⟨mid_clock s k h1, h2, hGc s k h3, h4⟩
  have hfj2 : ScanRun.Fresh "rj" (("rok", bw (decide (a.take 0 = b.take 0))) :: vs) = true := by
    simp only [ScanRun.Fresh, List.all_cons] at hfj ⊢; simp [hfj]
  refine frag_append (xs := [_]) (mid_put o h (y := "rok") hrok hlo
    (E := .op .add (.var "jz") (.const (.ofNat 64 1))) rfl (F := fun u => ScanRun.Vals u vs ∧ G u)
    (F' := fun u => ScanRun.Vals u (("rok", bw (decide (a.take 0 = b.take 0))) :: vs) ∧ G u)
    (fun s k ⟨h1, h2⟩ => ⟨h1, hGc s k h2⟩) fun u hu ⟨hvs, hg⟩ => ⟨_, by simp [eval, jz_kept h hu.kept, bw],
      ScanRun.vals_cons hvs hfo _, hGs u _ _ (by decide) hg⟩) ?_
  refine frag_append (xs := [_]) (frag_conseq (mid_put o h (y := "rj") hrj hlj
    (E := .op .add (.var "jz") (.const (.ofNat 64 0))) rfl
    (F := fun u => ScanRun.Vals u (("rok", bw (decide (a.take 0 = b.take 0))) :: vs) ∧ G u)
    (F' := fun u => ScanRun.Vals u (("rj", .ofNat 64 0) :: ("rok", bw (decide (a.take 0 = b.take 0))) :: vs) ∧ G u)
    (fun s k ⟨h1, h2⟩ => ⟨h1, hGc s k h2⟩) fun u hu ⟨hvs, hg⟩ => ⟨_, by simp [eval, jz_kept h hu.kept],
      ScanRun.vals_cons hvs hfj2 _, hGs u _ _ (by decide) hg⟩) (fun u h => h) fun u ⟨hu, hvs, hg⟩ => (⟨hu, hvs, hg,
          Nat.zero_le _⟩ : I 0 u))
    ?_
  have htake : ∀ j (hj : j < a.length), (a.take (j + 1) = b.take (j + 1)) ↔
      (a.take j = b.take j ∧ a[j] = b[j]'(by omega)) :=
    fun j hj => by
      rw [List.take_succ_eq_append_getElem hj, List.take_succ_eq_append_getElem (by omega : j < b.length)]
      constructor
      · intro e
        have := List.append_inj e (by simp; omega)
        exact ⟨this.1, by simpa using this.2⟩
      · rintro ⟨e1, e2⟩; rw [e1, e2]
  have hfr : ∀ j, ScanRun.Fresh "rj" (("rok", bw (decide (a.take j = b.take j))) :: vs) = true := fun j => by
    simp only [ScanRun.Fresh, List.all_cons] at hfj ⊢; simp [hfj]
  have hbody : ∀ j, decide (j < a.length) = true → Frag o
      [.ite (ScanProg.ne (.loadb (Syntax.eAdd (Syntax.atOff (Syntax.v "rcp") 8) (Syntax.v "rj")))
          (.loadb (Syntax.eAdd (Syntax.eAdd (Syntax.v "rwp") (Syntax.v "rga")) (Syntax.v "rj"))))
        [.assign "rok" (ScanProg.lit 0)] [],
       ScanProg.inc "rj"] (I j) (I (j + 1)) := fun j hj => by
    simp only [decide_eq_true_eq] at hj
    have hjb : j < b.length := by omega
    let N : Assn σ := fun u => Mid A cfg J r s0 ws os l u ∧
      ScanRun.Vals u (("rj", .ofNat 64 j) :: ("rok", bw (decide (a.take (j + 1) = b.take (j + 1)))) :: vs) ∧ G u ∧
        j + 1 ≤ a.length
    have hNc : Safe.ClockFree N := fun s k ⟨h1, h2, h3, h4⟩ => ⟨mid_clock s k h1, h2, hGc s k h3, h4⟩
    have hev : ∀ u, I j u → eval u (.cmp .equal (.cmp .equal
        (.loadByte (.op .add (.op .add (.var "rcp") (.const (.ofNat 64 8))) (.var "rj")))
        (.loadByte (.op .add (.op .add (.var "rwp") (.var "rga")) (.var "rj")))) (.const 0)) =
          some (bw (decide (a[j].toNat ≠ (b[j]'hjb).toNat))) := fun u ⟨_, hvs, hg, _⟩ => by
      have hj' := vals_lookup hvs (lookup_head _ _ _)
      have hp : ((("rj", BitVec.ofNat 64 j) :: ("rok", bw (decide (a.take j = b.take j))) :: vs)).lookup "rcp" =
          some pa := by rw [lookup_cons_ne (by decide), lookup_cons_ne (by decide), hrcp]
      have hw : ((("rj", BitVec.ofNat 64 j) :: ("rok", bw (decide (a.take j = b.take j))) :: vs)).lookup "rwp" =
          some pw := by rw [lookup_cons_ne (by decide), lookup_cons_ne (by decide), hrwp]
      obtain ⟨w, hgw, hbytes⟩ := hB u hg
      refine ScanRun.e_ne (x := a[j].toNat) (y := (b[j]'hjb).toNat) (by have := a[j].isLt; omega)
        (by have := (b[j]'hjb).isLt; omega) ?_ ?_
      · simp only [eval, vals_lookup hvs hp, hj', hA u hg j hj]; rw [Bytes.setWidth8_64]
      · simp only [eval, vals_lookup hvs hw, hgw, hj', hbytes j hjb]; rw [Bytes.setWidth8_64]
    refine frag_append (xs := [_]) (M := N) (frag_if o rfl (lowK_any _ (k := .skip) (c := _) rfl) (fun k => ⟨k, rfl⟩)
      rfl rfl hNc (b := decide (a[j].toNat ≠ (b[j]'hjb).toNat)) hev (fun hne => ?_) fun heq => ?_) ?_
    · -- the octets differ: the names do
      simp only [decide_eq_true_eq] at hne
      have hd : a.take (j + 1) ≠ b.take (j + 1) := fun e => hne (by rw [((htake j hj).mp e).2])
      refine set_frag o (E := .op .add (.var "jz") (.const (.ofNat 64 0))) rfl hNc fun u ⟨hu, hvs, hg, _⟩ =>
        ⟨0, by simp [eval, jz_kept h hu.kept], kept_has hu.kept (h.bound "rok" (by decide)), mid_setL hu hrok hlo _,
          ?_, hGs u _ _ (by decide) hg, by omega⟩
      have := ScanRun.vals_update (pre := [("rj", BitVec.ofNat 64 j)]) hvs (by simp [ScanRun.Fresh]) (hfo) 0
      simpa [hd, bw] using this
    · -- the same: as far as they are compared
      simp only [decide_eq_false_iff_not, Decidable.not_not] at heq
      have he : a[j] = b[j]'hjb := BitVec.eq_of_toNat_eq heq
      exact frag_nil o fun u ⟨hu, hvs, hg, _⟩ => ⟨hu, by
        have e : decide (a.take (j + 1) = b.take (j + 1)) = decide (a.take j = b.take j) := by
          rw [decide_eq_decide]; rw [htake j hj]; simp [he]
        rw [e]; exact hvs, hg, by omega⟩
    · exact frag_conseq (mid_put o h (y := "rj") hrj hlj (E := .op .add (.var "rj") (.const (.ofNat 64 1))) rfl
        (F := fun u => ScanRun.Vals u (("rj", .ofNat 64 j) ::
          ("rok", bw (decide (a.take (j + 1) = b.take (j + 1)))) :: vs) ∧ G u ∧ j + 1 ≤ a.length)
        (F' := fun u => ScanRun.Vals u (("rj", .ofNat 64 (j + 1)) ::
          ("rok", bw (decide (a.take (j + 1) = b.take (j + 1)))) :: vs) ∧ G u ∧ j + 1 ≤ a.length)
        (fun s k ⟨h1, h2, h3⟩ => ⟨h1, hGc s k h2, h3⟩) fun u _ ⟨hvs, hg, hj1⟩ => ⟨.ofNat 64 (j + 1), by
          simp only [eval, vals_lookup hvs (lookup_head _ _ _)]; rw [BitVec.ofNat_add],
          vals_head hvs (hfr (j + 1)) _, hGs u _ _ (by decide) hg, hj1⟩) (fun u ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, h4⟩)
        fun u ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, h4⟩
  refine frag_conseq (frag_count o (c := Syntax.eLt (Syntax.v "rj") (Syntax.v "rgl"))
    (C := .cmp .less (.var "rj") (.var "rgl")) rfl (lowK_any _ (k := .skip) (c := _) rfl) hIc
    (fun j => noDecl (P' := I j) _ rfl) (g := fun j => decide (j < a.length)) (fun j u ⟨_, hvs, _, _⟩ => by
      have hl' : ((("rj", BitVec.ofNat 64 j) :: ("rok", bw (decide (a.take j = b.take j))) :: vs)).lookup "rgl" =
          some (.ofNat 64 a.length) := by rw [lookup_cons_ne (by decide), lookup_cons_ne (by decide), hrgl]
      rw [FramerCode.eval_lt (t := u) (a := .var "rj") (b := .var "rgl") (x := j) (y := a.length) (by omega)
        (by omega) (vals_lookup hvs (lookup_head _ _ _)) (vals_lookup hvs hl')]; rfl) hbody 0) (fun _ h => h) ?_
  intro u ⟨j, ⟨hu, hvs, hg, hjl⟩, hgj⟩
  have : j = a.length := by simp only [decide_eq_false_iff_not] at hgj; omega
  subst this
  refine ⟨hu, ?_, hg⟩
  have e : decide (a.take a.length = b.take a.length) = decide (a = b) := by
    rw [List.take_length, hab, List.take_length]
  rw [← e]; exact hvs

/-! ## A group sought in the configuration -/

/-- **A group sought among the configuration's**: `rx` its place, as `groupIx` finds it. -/
theorem search_frag (o : Oracle σ) {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ}
    (h : PBase A s0) {ws : Nat → Word} {os : List (Nat × Word)} {l : List (String × Value)}
    (hl : ScanRun.Outside ["rok", "rj", "rcp", "rx", "rc"] l = true) {name : Bytes} (hnl : name.length ≤ 64)
    (hcnt : cfg.groups.length ≤ groupsMax)
    (hshort : ∀ g (hg : g < cfg.groups.length), cfg.groups[g].length ≤ groupNameMax) {pw : Word}
    {vs : List (String × Value)}
    (hfv : ScanRun.Outside ["rok", "rj", "rcp", "rx", "rc"] vs = true) (hrwp : vs.lookup "rwp" = some pw)
    (hrgl : vs.lookup "rgl" = some (.ofNat 64 name.length))
    (hrgn : vs.lookup "rgn" = some (.ofNat 64 cfg.groups.length))
    {G : Assn σ} (hGc : Safe.ClockFree G) (hGs : ∀ u y v, y ∈ ["rok", "rj", "rcp", "rx", "rc"] → G u → G (setL u y v))
    (hB : ∀ u, G u → ∃ w, u.locals "rga" = some w ∧ ∀ j (hj : j < name.length),
      memLoadByte u.memory u.memaddrs u.be (pw + w + BitVec.ofNat 64 j) = some name[j]) :
    Frag o [.while (Syntax.eLt (Syntax.v "rc") (Syntax.v "rgn"))
        [.assign "rcp" (Syntax.eAdd (Syntax.atOff rp rGroups) (Syntax.eMul (Syntax.v "rc") (Syntax.n rGroupSlot))),
         .ite (Syntax.eEq (.loadw 1 (Syntax.v "rcp")) (Syntax.v "rgl"))
           [.assign "rok" (ScanProg.lit 1), .assign "rj" (ScanProg.lit 0),
            .while (Syntax.eLt (Syntax.v "rj") (Syntax.v "rgl"))
              [.ite (ScanProg.ne (.loadb (Syntax.eAdd (Syntax.atOff (Syntax.v "rcp") 8) (Syntax.v "rj")))
                  (.loadb (Syntax.eAdd (Syntax.eAdd (Syntax.v "rwp") (Syntax.v "rga")) (Syntax.v "rj"))))
                [.assign "rok" (ScanProg.lit 0)] [],
               ScanProg.inc "rj"],
            .ite (Syntax.v "rok") [.assign "rx" (Syntax.v "rc")] []] [],
         ScanProg.inc "rc"]]
      (fun u => Mid A cfg J r s0 ws os l u ∧
        ScanRun.Vals u (("rc", .ofNat 64 0) :: ("rx", .ofNat 64 (ixUpTo cfg name 0)) :: vs) ∧ G u)
      (fun u => Mid A cfg J r s0 ws os l u ∧
        ScanRun.Vals u (("rc", .ofNat 64 cfg.groups.length) ::
          ("rx", .ofNat 64 (ixUpTo cfg name cfg.groups.length)) :: vs) ∧ G u) := by
  have hn := nums
  have hfr : ∀ y ∈ ["rok", "rj", "rcp", "rx", "rc"], ScanRun.Fresh y vs = true :=
    fun y hy => ScanRun.fresh_of_outside hfv hy
  have hfl : ∀ y ∈ ["rok", "rj", "rcp", "rx", "rc"], ScanRun.Fresh y l = true :=
    fun y hy => ScanRun.fresh_of_outside hl hy
  let I (k : Nat) : Assn σ := fun u => Mid A cfg J r s0 ws os l u ∧
    ScanRun.Vals u (("rc", .ofNat 64 k) :: ("rx", .ofNat 64 (ixUpTo cfg name k)) :: vs) ∧ G u ∧
      k ≤ cfg.groups.length
  have hIc : ∀ k, Safe.ClockFree (I k) := fun _ s k ⟨h1, h2, h3, h4⟩ => ⟨mid_clock s k h1, h2, hGc s k h3, h4⟩
  have lk : ∀ (k : Nat) (x : String) (w : Value), x ≠ "rc" → x ≠ "rx" → vs.lookup x = some w →
      ((("rc", BitVec.ofNat 64 k) :: ("rx", BitVec.ofNat 64 (ixUpTo cfg name k)) :: vs)).lookup x = some w :=
    fun k x w h1 h2 h3 => by rw [lookup_cons_ne h1, lookup_cons_ne h2, h3]
  have hbody : ∀ k, decide (k < cfg.groups.length) = true → Frag o
      [.assign "rcp" (Syntax.eAdd (Syntax.atOff rp rGroups) (Syntax.eMul (Syntax.v "rc") (Syntax.n rGroupSlot))),
       .ite (Syntax.eEq (.loadw 1 (Syntax.v "rcp")) (Syntax.v "rgl"))
         [.assign "rok" (ScanProg.lit 1), .assign "rj" (ScanProg.lit 0),
          .while (Syntax.eLt (Syntax.v "rj") (Syntax.v "rgl"))
            [.ite (ScanProg.ne (.loadb (Syntax.eAdd (Syntax.atOff (Syntax.v "rcp") 8) (Syntax.v "rj")))
                (.loadb (Syntax.eAdd (Syntax.eAdd (Syntax.v "rwp") (Syntax.v "rga")) (Syntax.v "rj"))))
              [.assign "rok" (ScanProg.lit 0)] [],
             ScanProg.inc "rj"],
          .ite (Syntax.v "rok") [.assign "rx" (Syntax.v "rc")] []] [],
       ScanProg.inc "rc"] (I k) (I (k + 1)) := fun k hk => by
    simp only [decide_eq_true_eq] at hk
    have hk64 : k < groupsMax := by omega
    let pa := at_ A (rGroups + k * rGroupSlot)
    have hkm : k * rGroupSlot ≤ 63 * 72 := Nat.mul_le_mul (by omega) (by omega)
    let L := ("rc", BitVec.ofNat 64 k) :: ("rx", BitVec.ofNat 64 (ixUpTo cfg name k)) :: vs
    let L1 := ("rc", BitVec.ofNat 64 k) :: ("rx", BitVec.ofNat 64 (ixUpTo cfg name (k + 1))) :: vs
    have hgk : cfg.groups.getD k [] = cfg.groups[k] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; rfl
    -- the configuration's group's place
    refine frag_append (xs := [_]) (M := fun u => Mid A cfg J r s0 ws os l u ∧ ScanRun.Vals u (("rcp", pa) :: L) ∧
      G u ∧ k < cfg.groups.length) (frag_conseq (mid_put o h (y := "rcp") (by decide) (hfl _ (by decide))
        (E := .op .add (.op .add (.var "rsc") (.const (.ofNat 64 rGroups)))
          (.mul (.var "rc") (.const (.ofNat 64 rGroupSlot)))) rfl
        (F := fun u => ScanRun.Vals u L ∧ G u ∧ k < cfg.groups.length)
        (F' := fun u => ScanRun.Vals u (("rcp", pa) :: L) ∧ G u ∧ k < cfg.groups.length)
        (fun s k' ⟨h1, h2, h3⟩ => ⟨h1, hGc s k' h2, h3⟩) fun u hu ⟨hvs, hg, hk'⟩ => ⟨pa,
          index_eval (rsc_kept h hu.kept) (vals_lookup hvs (lookup_head _ _ _)) rGroups rGroupSlot,
          ScanRun.vals_cons hvs (fresh_cons (by decide) (fresh_cons (by decide) (hfr "rcp" (by decide)))) _,
          hGs u _ _ (by decide) hg, hk'⟩)
        (fun u ⟨h1, h2, h3, _⟩ => ⟨h1, h2, h3, hk⟩) fun _ h => h) ?_
    let N : Assn σ := fun u => Mid A cfg J r s0 ws os l u ∧ ScanRun.Vals u (("rcp", pa) :: L1) ∧ G u ∧
      k < cfg.groups.length
    have hNc : Safe.ClockFree N := fun s k ⟨h1, h2, h3, h4⟩ => ⟨mid_clock s k h1, h2, hGc s k h3, h4⟩
    have hdom : ∀ u, Mid A cfg J r s0 ws os l u → u.memaddrs pa = true := fun u hu =>
      have h72 : k * rGroupSlot = k * 72 := rfl
      area_dom h hu.kept.memaddrs (by omega) (by rw [h72]; omega)
    refine frag_append (xs := [_]) (M := N) (frag_if o (C := .cmp .equal (.loadWord (.var "rcp")) (.var "rgl")) rfl
      (lowK_any _ (k := .skip) (c := _) rfl) (fun k => ⟨k, rfl⟩) rfl rfl hNc
      (b := decide (cfg.groups[k].length = name.length)) (fun u ⟨hu, hvs, _, _⟩ => by
        have hp : eval u (.loadWord (.var "rcp")) = some (.ofNat 64 cfg.groups[k].length) := by
          simp only [eval, vals_lookup hvs (lookup_head _ _ _), hdom u hu, if_true]
          exact congrArg some (hu.rest.config.len k hk)
        exact FramerCode.eval_eq (t := u) (x := cfg.groups[k].length) (y := name.length)
          (Nat.lt_of_le_of_lt (hu.rest.config.short k hk) (by decide)) (by omega) hp
          (vals_lookup hvs (by rw [lookup_cons_ne (by decide)]; exact lk k _ _ (by decide) (by decide) hrgl)))
      (fun hb => ?_) fun hb => ?_) ?_
    · -- the same length: the names compared
      simp only [decide_eq_true_eq] at hb
      have hl2 : ScanRun.Outside ["rok", "rj"] l = true := by
        simp only [ScanRun.Outside, List.all_eq_true] at hl ⊢
        intro q hq; have := hl q hq; simp only [List.contains_cons, List.contains_nil, Bool.or_false,
          Bool.not_or, Bool.and_eq_true] at this ⊢; exact ⟨this.1, this.2.1⟩
      let vs' := ("rcp", pa) :: L
      have hlk : ∀ x w, x ≠ "rcp" → x ≠ "rc" → x ≠ "rx" → vs.lookup x = some w → vs'.lookup x = some w :=
        fun x w h0 h1 h2 h3 => by rw [lookup_cons_ne h0]; exact lk k x w h1 h2 h3
      let G' : Assn σ := fun u => CfgAt A cfg u ∧ G u ∧ k < cfg.groups.length
      refine frag_append (xs := [_, _, _]) (frag_conseq (nameCmp_frag o h hl2 (a := cfg.groups[k]) (b := name)
        hb (by have := hshort k hk; omega) (vs := vs') (fresh_cons (by decide) (fresh_cons (by decide)
          (fresh_cons (by decide) (hfr _ (by decide))))) (fresh_cons (by decide) (fresh_cons (by decide)
          (fresh_cons (by decide) (hfr _ (by decide))))) (lookup_head _ _ _)
        (hlk _ _ (by decide) (by decide) (by decide) hrwp)
        (by rw [hb]; exact hlk _ _ (by decide) (by decide) (by decide) hrgl) (G := G')
        (fun s k' ⟨h1, h2, h3⟩ => ⟨cfgAt_congr h1 rfl rfl rfl, hGc s k' h2, h3⟩)
        (fun u y v hy ⟨h1, h2, h3⟩ => ⟨cfgAt_congr h1 rfl rfl rfl, hGs u y v (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hy ⊢; rcases hy with rfl | rfl <;> simp) h2, h3⟩)
        (fun u ⟨hc, _, _⟩ j hj => by
          have := hc.name k hk j hj
          rw [show pa + BitVec.ofNat 64 8 + BitVec.ofNat 64 j = at_ A (rGroups + k * rGroupSlot + 8 + j) by
            simp only [pa]; rw [at_add, at_add]]
          exact this)
        (fun u ⟨_, hg, _⟩ => hB u hg)) (fun u ⟨hu, hvs, hg, hk'⟩ => ⟨hu, hvs, hu.rest.config, hg, hk'⟩)
        fun _ h => h) ?_
      -- its place, when the names are the same
      have hfx : ScanRun.Fresh "rx" [("rj", BitVec.ofNat 64 cfg.groups[k].length),
          ("rok", bw (decide (cfg.groups[k] = name))), ("rcp", pa), ("rc", BitVec.ofNat 64 k)] = true := by
        simp [ScanRun.Fresh]
      refine frag_conseq (ScanRun.flagIf_frag o (x := "rok") (lowK_any _ (k := .skip) (c := _) rfl) rfl
        (b := decide (cfg.groups[k] = name))
        (Q := fun u => Mid A cfg J r s0 ws os l u ∧ ScanRun.Vals u
          (("rj", BitVec.ofNat 64 cfg.groups[k].length) :: ("rok", bw (decide (cfg.groups[k] = name))) ::
            ("rcp", pa) :: L1) ∧ G' u)
        (fun s k' ⟨h1, h2, h3, h4, h5⟩ => ⟨mid_clock s k' h1, h2, cfgAt_congr h3 rfl rfl rfl, hGc s k' h4, h5⟩)
        (fun u ⟨_, hvs, _⟩ => vals_lookup hvs (by rw [lookup_cons_ne (by decide), lookup_head])) (fun he => ?_)
        fun he u ⟨hu, hvs, hg⟩ => ?_) (fun _ h => h) fun u ⟨hu, hvs, _, hg, hk'⟩ => ⟨hu, fun q hq => hvs q (by
          simp only [List.mem_cons] at hq ⊢; exact .inr (.inr hq)), hg, hk'⟩
      · simp only [decide_eq_true_eq] at he
        have e : ixUpTo cfg name (k + 1) = k := by rw [ix_succ, if_pos (by rw [hgk, he])]
        refine set_frag o (E := .var "rc") rfl (fun s k' ⟨h1, h2, h3, h4, h5⟩ =>
          ⟨mid_clock s k' h1, h2, cfgAt_congr h3 rfl rfl rfl, hGc s k' h4, h5⟩) fun u ⟨hu, hvs, hg⟩ =>
            ⟨_, vals_lookup hvs (by rw [lookup_cons_ne (by decide), lookup_cons_ne (by decide),
              lookup_cons_ne (by decide), lookup_head]), kept_has hu.kept (h.bound "rx" (by decide)),
              mid_setL hu (by decide) (hfl _ (by decide)) _, ?_,
              ⟨cfgAt_congr hg.1 rfl rfl rfl, hGs u _ _ (by decide) hg.2.1, hg.2.2⟩⟩
        have := ScanRun.vals_update (pre := [("rj", BitVec.ofNat 64 cfg.groups[k].length),
          ("rok", bw (decide (cfg.groups[k] = name))), ("rcp", pa), ("rc", BitVec.ofNat 64 k)]) hvs hfx
          (hfr _ (by decide)) (.ofNat 64 k)
        simpa [L1, e] using this
      · simp only [decide_eq_false_iff_not] at he
        have hne : cfg.groups.getD k [] ≠ name := by rw [hgk]; exact he
        have e : ixUpTo cfg name (k + 1) = ixUpTo cfg name k := by rw [ix_succ, if_neg hne]
        exact ⟨hu, by simp only [L1, e]; exact hvs, hg⟩
    · -- lengths that differ: names that do
      simp only [decide_eq_false_iff_not] at hb
      have hne : cfg.groups.getD k [] ≠ name := by rw [hgk]; intro e; exact hb (by rw [e])
      have e : ixUpTo cfg name (k + 1) = ixUpTo cfg name k := by rw [ix_succ, if_neg hne]
      exact frag_nil o fun u ⟨hu, hvs, hg, hk'⟩ => ⟨hu, by simp only [L1, e]; exact hvs, hg, hk'⟩
    · -- the next of the configuration's groups
      have hfc : ScanRun.Fresh "rc" [("rcp", pa)] = true := by simp [ScanRun.Fresh]
      refine set_frag o (E := .op .add (.var "rc") (.const (.ofNat 64 1))) rfl (hIc (k + 1)) fun u ⟨hu, hvs, hg, _⟩ =>
        ⟨.ofNat 64 (k + 1), by
          simp only [eval, vals_lookup hvs (by rw [lookup_cons_ne (show "rc" ≠ "rcp" by decide), lookup_head])]
          rw [BitVec.ofNat_add],
          kept_has hu.kept (h.bound "rc" (by decide)), mid_setL hu (by decide) (hfl _ (by decide)) _, ?_,
          hGs u _ _ (by decide) hg, by omega⟩
      have := ScanRun.vals_update (pre := [("rcp", pa)]) hvs hfc
        (fresh_cons (by decide) (hfr _ (by decide))) (.ofNat 64 (k + 1))
      exact fun q hq => this q (by simp only [List.mem_cons, List.cons_append, List.nil_append] at hq ⊢; exact .inr hq)
  refine frag_conseq (frag_count o (c := Syntax.eLt (Syntax.v "rc") (Syntax.v "rgn"))
    (C := .cmp .less (.var "rc") (.var "rgn")) rfl (lowK_any _ (k := .skip) (c := _) rfl) hIc
    (fun k => noDecl (P' := I k) _ rfl) (g := fun k => decide (k < cfg.groups.length)) (fun k u ⟨_, hvs, _, _⟩ => by
      rw [FramerCode.eval_lt (t := u) (a := .var "rc") (b := .var "rgn") (x := k) (y := cfg.groups.length) (by omega)
        (by omega) (vals_lookup hvs (lookup_head _ _ _)) (vals_lookup hvs (lk k _ _ (by decide) (by decide) hrgn))]
      rfl) hbody 0) (fun u ⟨hu, hvs, hg⟩ => ⟨hu, hvs, hg, Nat.zero_le _⟩) ?_
  intro u ⟨k, ⟨hu, hvs, hg, hk⟩, hgk⟩
  have : k = cfg.groups.length := by simp only [decide_eq_false_iff_not] at hgk; omega
  subst this; exact ⟨hu, hvs, hg⟩

/-! ## The first group the configuration lacks, noted -/

/-- What the area keeps of the first group the configuration lacks, while `Rest` has none. -/
def UnkNoted (A : Word) (r : RSt) (unk : Option Bytes) (u : PancakeState σ) : Prop :=
  ∀ x, unk = some x → r.unknown = none →
    u.memory (at_ A rUnknownLen) = .ofNat 64 x.length ∧ x.length ≤ groupNameMax ∧ BytesAt A rUnknownName x u

/-- A word of the first group's stored while there is none. -/
theorem unk_store (o : Oracle σ) {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ}
    (h : PBase A s0) (hun : r.unknown = none) {ws : Nat → Word} {os : List (Nat × Word)}
    {l : List (String × Value)} (hos : ∀ q ∈ os, rScan ≤ q.1 ∧ q.1 < rSlots) {x : Nat} (hx8 : x % 8 = 0)
    (hx : rUnknownLen ≤ x ∧ x < rTorn) {e : Syntax.PExpr} {E : PancakeExp} (he : Lower.lowerExp e = some E) {val : Word}
    {F F' : Assn σ} (hF'c : Safe.ClockFree F') (hv : ∀ u, Mid A cfg J r s0 ws os l u → F u → eval u E = some val)
    (hF : ∀ u, Mid A cfg J r s0 ws os l u → F u → F' (stW u A x val)) :
    Frag o [rset x e] (fun u => Mid A cfg J r s0 ws os l u ∧ F u) (fun u => Mid A cfg J r s0 ws os l u ∧ F' u) := by
  have hx0 : x ≠ 0 := by simp only [rUnknownLen, rUnknown] at hx; omega
  exact far_store o h hos (.inl ⟨hx.1, hx.2, hun⟩) hx8 (D := .op .add (.var "rsc") (.const (.ofNat 64 x)))
    (by simp [rp, Syntax.atOff, hx0, Lower.lowerExp, Syntax.eAdd, Syntax.v, Syntax.n]) he hF'c
    (fun u hu hf => ⟨by simp only [eval, rsc_kept h hu.kept]; rfl, hv u hu hf⟩) hF

/-- An octet of the first group's name stored while there is none. -/
theorem unk_storeb (o : Oracle σ) {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ}
    (h : PBase A s0) (hun : r.unknown = none) {ws : Nat → Word} {os : List (Nat × Word)}
    {l : List (String × Value)} (hos : ∀ q ∈ os, rScan ≤ q.1 ∧ q.1 < rSlots) {z : Nat}
    (hz : rUnknownName ≤ z ∧ z < rTorn) {d e : Syntax.PExpr} {D E : PancakeExp} (hd : Lower.lowerExp d = some D)
    (he : Lower.lowerExp e = some E) {b : BitVec 8} {F F' : Assn σ} (hF'c : Safe.ClockFree F')
    (hv : ∀ u, Mid A cfg J r s0 ws os l u → F u → eval u D = some (at_ A z) ∧ eval u E = some (b.setWidth 64))
    (hF : ∀ u, Mid A cfg J r s0 ws os l u → F u → F' { u with memory := putByte u.memory u.be (at_ A z) b }) :
    Frag o [.storeb d e] (fun u => Mid A cfg J r s0 ws os l u ∧ F u) (fun u => Mid A cfg J r s0 ws os l u ∧ F' u) := by
  have hn := nums
  exact far_storeb o h hos (.inl ⟨by omega, by omega, hun⟩) (by omega) hd he hF'c hv hF

theorem mid_ws {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ} {ws ws' : Nat → Word}
    {os : List (Nat × Word)} {l : List (String × Value)} {u : PancakeState σ} (hu : Mid A cfg J r s0 ws os l u)
    (hfg : ∀ x ∈ scalarOffs, ws x = ws' x) : Mid A cfg J r s0 ws' os l u :=
  { hu with words := words_ext hu.words hfg }

theorem upd_same {ws : Nat → Word} {x : Nat} {v : Word} (h : ws x = v) : ∀ y ∈ scalarOffs, ws y = upd ws x v y :=
  fun y _ => by simp only [upd]; split <;> simp_all

/-- **A group the configuration lacks noted**, the first: its name copied while none is. -/
theorem unknownNote_frag (o : Oracle σ) {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ}
    (h : PBase A s0) {ws : Nat → Word} {os : List (Nat × Word)} {l : List (String × Value)}
    (hl : ScanRun.Fresh "rj" l = true) (hos : ∀ q ∈ os, rScan ≤ q.1 ∧ q.1 < rSlots) {name : Bytes}
    (hnl : name.length ≤ groupNameMax) {pw : Word} {ix : Nat} {vs : List (String × Value)}
    (hfj : ScanRun.Fresh "rj" vs = true) (hrwp : vs.lookup "rwp" = some pw)
    (hrgl : vs.lookup "rgl" = some (.ofNat 64 name.length))
    (hrx : vs.lookup "rx" = some (.ofNat 64 ix)) (hix : ix ≤ groupsMax) {unk : Option Bytes}
    (hwsu : ws rUnknown = bw unk.isSome) (hext : ∀ x, r.unknown = some x → unk = some x)
    {G : Assn σ} (hGc : Safe.ClockFree G) (hGs : ∀ u v, G u → G (setL u "rj" v))
    (hGw : ∀ u x v, G u → rUnknown ≤ x → x < rTorn → G (stW u A x v))
    (hGb : ∀ u z b, G u → rUnknownName ≤ z → z < rTorn → G { u with memory := putByte u.memory u.be (at_ A z) b })
    (hB : ∀ u, G u → ∃ w, u.locals "rga" = some w ∧ ∀ j (hj : j < name.length),
      memLoadByte u.memory u.memaddrs u.be (pw + w + BitVec.ofNat 64 j) = some name[j]) :
    Frag o [.ite (Syntax.eEq (Syntax.v "rx") (Syntax.n groupsMax))
        [.ite (rw rUnknown) []
          [rset rUnknown (Syntax.n 1), rset rUnknownLen (Syntax.v "rgl"), .assign "rj" (ScanProg.lit 0),
           .while (Syntax.eLt (Syntax.v "rj") (Syntax.v "rgl"))
             [.storeb (Syntax.eAdd (Syntax.atOff rp rUnknownName) (Syntax.v "rj"))
                (.loadb (Syntax.eAdd (Syntax.eAdd (Syntax.v "rwp") (Syntax.v "rga")) (Syntax.v "rj"))),
              ScanProg.inc "rj"]]] []]
      (fun u => Mid A cfg J r s0 ws os l u ∧ ScanRun.Vals u vs ∧ G u ∧ UnkNoted A r unk u)
      (fun u => Mid A cfg J r s0 (upd ws rUnknown (bw (unk <|> if ix = groupsMax then some name else none).isSome))
        os l u ∧ ScanRun.Vals u vs ∧ G u ∧ UnkNoted A r (unk <|> if ix = groupsMax then some name else none) u) := by
  have hn := nums
  generalize hU : (unk <|> if ix = groupsMax then some name else none) = unk'
  have hQc : Safe.ClockFree (fun u => Mid A cfg J r s0 (upd ws rUnknown (bw unk'.isSome)) os l u ∧
      ScanRun.Vals u vs ∧ G u ∧ UnkNoted A r unk' u) :=
  fun s k ⟨h1, h2, h3, h4⟩ => ⟨mid_clock s k h1, h2, hGc s k h3, h4⟩
  refine frag_if o (C := .cmp .equal (.var "rx") (.const (.ofNat 64 groupsMax))) rfl
    (lowK_any _ (k := .skip) (c := _) rfl) (fun k => ⟨k, rfl⟩) rfl rfl hQc (b := decide (ix = groupsMax))
    (fun u ⟨_, hvs, _, _⟩ => FramerCode.eval_eq (t := u) (x := ix) (y := groupsMax) (by omega) (by decide)
      (vals_lookup hvs hrx) rfl) (fun hx => ?_) fun hx => ?_
  rotate_left
  · -- a group the configuration has: nothing noted
    simp only [decide_eq_false_iff_not] at hx
    have e : unk' = unk := by rw [← hU]; simp [hx]
    exact frag_nil o fun u ⟨hu, hvs, hg, hf⟩ => ⟨mid_ws hu (by rw [e]; exact upd_same hwsu), hvs, hg,
        by rw [e]; exact hf⟩
  simp only [decide_eq_true_eq] at hx
  refine frag_if o (C := rwE rUnknown) (rw_lower (by decide)) (fun k => ⟨k, rfl⟩)
    (lowK_any _ (k := .skip) (c := _) rfl) rfl rfl hQc (b := unk.isSome)
    (fun u ⟨hu, _, _, _⟩ => by rw [mid_rw h hu (by decide) (rw_lower (by decide)), hwsu]) (fun hs => ?_) fun hs => ?_
  · -- one noted already
    have e : unk' = unk := by obtain ⟨x, rfl⟩ := Option.isSome_iff_exists.mp hs; rw [← hU]; rfl
    exact frag_nil o fun u ⟨hu, hvs, hg, hf⟩ => ⟨mid_ws hu (by rw [e]; exact upd_same hwsu), hvs, hg,
        by rw [e]; exact hf⟩
  -- the first: noted
  have hu0 : unk = none := by cases unk <;> simp_all
  have hr0 : r.unknown = none := by
    cases e : r.unknown with
    | none => rfl
    | some x => rw [hext x e] at hu0; cases hu0
  have e : unk' = some name := by rw [← hU]; simp [hu0, hx]
  rw [e]
  refine frag_conseq (P0 := fun u => Mid A cfg J r s0 ws os l u ∧ ScanRun.Vals u vs ∧ G u) ?_
    (fun u ⟨h1, h2, h3, _⟩ => ⟨h1, h2, h3⟩) fun _ h => h
  let ws1 := upd ws rUnknown (.ofNat 64 1)
  let LW (u : PancakeState σ) : Prop := u.memory (at_ A rUnknownLen) = .ofNat 64 name.length
  refine frag_append (xs := [_]) (mid_set_and o h (x := rUnknown) (by decide) (E := .const (.ofNat 64 1)) rfl
    (val := .ofNat 64 1) (F := fun u => ScanRun.Vals u vs ∧ G u) (fun _ _ _ => rfl)
    (fun s k ⟨h1, h2⟩ => ⟨h1, hGc s k h2⟩) fun u v ⟨h1, h2⟩ => ⟨h1, hGw u _ v h2 (by omega) (by omega)⟩) ?_
  refine frag_append (xs := [_]) (unk_store o h hr0 hos (x := rUnknownLen) (by decide) (by omega) (e := Syntax.v "rgl")
    (E := .var "rgl") rfl (val := .ofNat 64 name.length) (F := fun u => ScanRun.Vals u vs ∧ G u)
    (F' := fun u => ScanRun.Vals u vs ∧ G u ∧ LW u) (fun s k ⟨h1, h2, h3⟩ => ⟨h1, hGc s k h2, h3⟩)
    (fun u _ ⟨hvs, _⟩ => ev_var (vals_lookup hvs hrgl))
    fun u _ ⟨hvs, hg⟩ => ⟨hvs, hGw u _ _ hg (by omega) (by omega),
      by show (stW u A rUnknownLen _).memory _ = _; simp [stW]⟩) ?_
  let I (j : Nat) : Assn σ := fun u => Mid A cfg J r s0 ws1 os l u ∧ ScanRun.Vals u (("rj", .ofNat 64 j) :: vs) ∧
    (G u ∧ LW u ∧ BytesAt A rUnknownName (name.take j) u ∧ j ≤ name.length)
  have hIc : ∀ j, Safe.ClockFree (I j) := fun _ s k ⟨h1, h2, h3, h4⟩ => ⟨mid_clock s k h1, h2, hGc s k h3, h4⟩
  refine frag_append (xs := [_]) (M := I 0) (frag_conseq (mid_put o h (y := "rj") (by decide) hl
    (E := .op .add (.var "jz") (.const (.ofNat 64 0))) rfl (F := fun u => ScanRun.Vals u vs ∧ G u ∧ LW u)
    (F' := fun u => ScanRun.Vals u (("rj", .ofNat 64 0) :: vs) ∧
      (G u ∧ LW u ∧ BytesAt A rUnknownName (name.take 0) u ∧ 0 ≤ name.length))
    (fun s k ⟨h1, h2, h3⟩ => ⟨h1, hGc s k h2, h3⟩) fun u hu ⟨hvs, hg, hlw⟩ => ⟨_, by simp [eval, jz_kept h hu.kept],
      ScanRun.vals_cons hvs hfj _, hGs u _ hg, hlw, fun i hi => absurd hi (by simp), Nat.zero_le _⟩)
    (fun u h => h) fun u ⟨h1, h2, h3⟩ => ⟨h1, h2, h3⟩) ?_
  have hbody : ∀ j, decide (j < name.length) = true → Frag o
      [.storeb (Syntax.eAdd (Syntax.atOff rp rUnknownName) (Syntax.v "rj"))
         (.loadb (Syntax.eAdd (Syntax.eAdd (Syntax.v "rwp") (Syntax.v "rga")) (Syntax.v "rj"))), ScanProg.inc "rj"]
      (I j) (I (j + 1)) := fun j hj => by
    simp only [decide_eq_true_eq] at hj
    have hlk : ∀ x w, x ≠ "rj" → vs.lookup x = some w → ((("rj", BitVec.ofNat 64 j) :: vs)).lookup x = some w :=
      fun x w h1 h2 => by rw [lookup_cons_ne h1, h2]
    refine frag_append (xs := [_]) (unk_storeb o h hr0 hos (z := rUnknownName + j) (by omega)
      (D := .op .add (.op .add (.var "rsc") (.const (.ofNat 64 rUnknownName))) (.var "rj"))
      (E := .loadByte (.op .add (.op .add (.var "rwp") (.var "rga")) (.var "rj"))) rfl rfl (b := name[j])
      (F := fun u => ScanRun.Vals u (("rj", .ofNat 64 j) :: vs) ∧
        (G u ∧ LW u ∧ BytesAt A rUnknownName (name.take j) u ∧ j ≤ name.length))
      (F' := fun u => ScanRun.Vals u (("rj", .ofNat 64 j) :: vs) ∧
        (G u ∧ LW u ∧ BytesAt A rUnknownName (name.take (j + 1)) u ∧ j + 1 ≤ name.length))
      (fun s k ⟨h1, h2, h3⟩ => ⟨h1, hGc s k h2, h3⟩) (fun u hu ⟨hvs, hg, _⟩ => ⟨by
        simp only [eval, rsc_kept h hu.kept, vals_lookup hvs (lookup_head _ _ _)]; rw [← at_add]; rfl, by
        obtain ⟨w, hgw, hbytes⟩ := hB u hg
        simp only [eval, vals_lookup hvs (hlk _ _ (by decide) hrwp), hgw,
          vals_lookup hvs (lookup_head _ _ _), hbytes j hj]⟩)
      fun u hu ⟨hvs, hg, hlw, hb, _⟩ => ⟨hvs, ?_, ?_, ?_, by omega⟩) ?_
    · exact hGb u _ _ hg (by omega) (by omega)
    · rw [putByte_stW h.hA]; show (stW u A _ _).memory _ = _
      rw [stW_word (by omega) (by omega) (by omega)]; exact hlw
    · have hl' : (name.take j).length = j := by simp; omega
      have := bytesAt_snoc (A := A) (z := rUnknownName) hb (by rw [hl']; omega) (by
        rw [hl', hu.kept.memaddrs]; exact h.dom _ (by omega)) name[j]
      rw [hl'] at this
      rwa [List.take_succ_eq_append_getElem hj]
    · exact frag_conseq (mid_put o h (y := "rj") (by decide) hl (E := .op .add (.var "rj") (.const (.ofNat 64 1))) rfl
        (F := fun u => ScanRun.Vals u (("rj", .ofNat 64 j) :: vs) ∧
          (G u ∧ LW u ∧ BytesAt A rUnknownName (name.take (j + 1)) u ∧ j + 1 ≤ name.length))
        (F' := fun u => ScanRun.Vals u (("rj", .ofNat 64 (j + 1)) :: vs) ∧
          (G u ∧ LW u ∧ BytesAt A rUnknownName (name.take (j + 1)) u ∧ j + 1 ≤ name.length))
        (fun s k ⟨h1, h2, h3⟩ => ⟨h1, hGc s k h2, h3⟩) fun u _ ⟨hvs, hg, hr⟩ => ⟨.ofNat 64 (j + 1), by
          simp only [eval, vals_lookup hvs (lookup_head _ _ _)]; rw [BitVec.ofNat_add],
          vals_head hvs hfj _, hGs u _ hg, hr⟩) (fun u ⟨h1, h2, h3⟩ => ⟨h1, h2, h3⟩) fun u ⟨h1, h2, h3⟩ => ⟨h1, h2, h3⟩
  refine frag_conseq (frag_count o (c := Syntax.eLt (Syntax.v "rj") (Syntax.v "rgl"))
    (C := .cmp .less (.var "rj") (.var "rgl")) rfl (lowK_any _ (k := .skip) (c := _) rfl) hIc
    (fun j => noDecl (P' := I j) _ rfl) (g := fun j => decide (j < name.length)) (fun j u ⟨_, hvs, _, _, _, _⟩ => by
      rw [FramerCode.eval_lt (t := u) (a := .var "rj") (b := .var "rgl") (x := j) (y := name.length) (by omega)
        (by omega) (vals_lookup hvs (lookup_head _ _ _)) (vals_lookup hvs (by rw [lookup_cons_ne (by decide), hrgl]))]
      rfl) hbody 0) (fun _ h => h) ?_
  intro u ⟨j, ⟨hu, hvs, hg, hlw, hb, hj⟩, hgj⟩
  have : j = name.length := by simp only [decide_eq_false_iff_not] at hgj; omega
  subst this
  rw [List.take_length] at hb
  exact ⟨hu, fun q hq => hvs q (List.mem_cons_of_mem _ hq), hg, fun x hx _ => by cases hx; exact ⟨hlw, hnl, hb⟩⟩

theorem slot_addr (A : Word) {i : Nat} (hi : i < capacity) :
    A + BitVec.ofNat 64 rSlots + (BitVec.ofNat 64 (i + 1) - BitVec.ofNat 64 1) * BitVec.ofNat 64 slotSize =
      at_ A (slotAt i) := by
  have hn := nums
  rw [BitVec.ofNat_sub_ofNat_of_le (i + 1) 1 (by decide) (by omega), Nat.add_sub_cancel, ← BitVec.ofNat_mul,
    BitVec.add_assoc, ← BitVec.ofNat_add]
  rfl

theorem recordRead_commit (cfg : Config) (r : RSt) (c : Commit) :
    RecoverSpec.recordRead cfg r (.commit c) =
      { r with commits := r.commits ++ [c],
               unknown := if r.commits.length + 1 ≤ capacity then r.unknown <|> RecoverSpec.unknownIn cfg c
                 else r.unknown } :=
  rfl

/-- A local of a commit read's set, listed. -/
theorem crPut_frag (o : Oracle σ) {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ}
    (h : PBase A s0) {ws : Nat → Word} {os : List (Nat × Word)} {l : List (String × Value)}
    (hl : ScanRun.Outside crNames l = true) (vs : List (String × Value)) (Q : Assn σ) (y : String) (e : Syntax.PExpr)
    (E : PancakeExp) (val : Value) (hy : y ∈ crNames) (hyv : ScanRun.Fresh y vs = true)
    (he : Lower.lowerExp e = some E) (hQs : ∀ u v, Q u → Q (setL u y v)) (hQc : Safe.ClockFree Q)
    (hv : ∀ u, Mid A cfg J r s0 ws os l u → ScanRun.Vals u vs → Q u → eval u E = some val) :
    Frag o [.assign y e] (fun u => Mid A cfg J r s0 ws os l u ∧ ScanRun.Vals u vs ∧ Q u)
      (fun u => Mid A cfg J r s0 ws os l u ∧ ScanRun.Vals u ((y, val) :: vs) ∧ Q u) :=
  frag_conseq (mid_put o h (y := y) (cr_step y hy) (ScanRun.fresh_of_outside hl hy) he
    (F := fun u => ScanRun.Vals u vs ∧ Q u) (F' := fun u => ScanRun.Vals u ((y, val) :: vs) ∧ Q u)
    (fun s k ⟨h1, h2⟩ => ⟨h1, hQc s k h2⟩) fun u hu ⟨hvs, hq⟩ => ⟨val, hv u hu hvs hq, ScanRun.vals_cons hvs hyv val,
      hQs u val hq⟩) (fun _ ⟨h1, h2, h3⟩ => ⟨h1, h2, h3⟩) fun _ ⟨h1, h2, h3⟩ => ⟨h1, h2, h3⟩

/-- A count of a commit read's one more. -/
theorem crBump_frag (o : Oracle σ) {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ}
    (h : PBase A s0) {ws : Nat → Word} {os : List (Nat × Word)} {l : List (String × Value)}
    (hl : ScanRun.Outside crNames l = true) (y : String) (vs : List (String × Value)) (Q : Assn σ) (j : Nat)
    (hy : y ∈ crNames) (hyv : ScanRun.Fresh y vs = true) (hQs : ∀ u v, Q u → Q (setL u y v))
    (hQc : Safe.ClockFree Q) :
    Frag o [ScanProg.inc y] (fun u => Mid A cfg J r s0 ws os l u ∧ ScanRun.Vals u ((y, .ofNat 64 j) :: vs) ∧ Q u)
      (fun u => Mid A cfg J r s0 ws os l u ∧ ScanRun.Vals u ((y, .ofNat 64 (j + 1)) :: vs) ∧ Q u) :=
  frag_conseq (mid_put o h (y := y) (cr_step y hy) (ScanRun.fresh_of_outside hl hy)
    (E := .op .add (.var y) (.const (.ofNat 64 1))) rfl
    (F := fun u => ScanRun.Vals u ((y, .ofNat 64 j) :: vs) ∧ Q u)
    (F' := fun u => ScanRun.Vals u ((y, .ofNat 64 (j + 1)) :: vs) ∧ Q u) (fun s k ⟨h1, h2⟩ => ⟨h1, hQc s k h2⟩)
    fun u _ ⟨hvs, hq⟩ => ⟨.ofNat 64 (j + 1), by
      simp only [eval, vals_lookup hvs (lookup_head y _ vs)]; rw [BitVec.ofNat_add],
      vals_head hvs hyv _, hQs u _ hq⟩) (fun _ ⟨h1, h2, h3⟩ => ⟨h1, h2, h3⟩) fun _ ⟨h1, h2, h3⟩ => ⟨h1, h2, h3⟩

/-! ## A commit's groups in its slot -/

/-- The words slot `S` holds once a commit read stores them: its number, its sizes, and its CRC with the
Message-ID's length and the count of groups. -/
def SlotWords (A : Word) (S : Nat) (c : Commit) (u : PancakeState σ) : Prop :=
  u.memory (at_ A (S + slotSeq)) = .ofNat 64 c.seq ∧
    u.memory (at_ A (S + slotSizes)) = (BitVec.ofNat 64 c.headerSize <<< 32) ||| .ofNat 64 c.fileSize ∧
    u.memory (at_ A (S + slotMisc)) =
      ((BitVec.ofNat 64 c.fileCrc <<< 16) ||| (BitVec.ofNat 64 c.messageId.length <<< 8)) ||| .ofNat 64 c.groups.length

/-- What a commit read keeps once it hashes: the commit's fields, its slot's words and its Message-ID there. -/
def HeadIn (A : Word) (o' : Nat) (pl : Bytes) (S : Nat) (c : Commit) (u : PancakeState σ) : Prop :=
  CommitIn A o' pl c u ∧ SlotWords A S c u ∧ BytesAt A (S + slotId) c.messageId u

theorem HeadIn.commit {A : Word} {o' : Nat} {pl : Bytes} {S : Nat} {c : Commit} {u : PancakeState σ}
    (h : HeadIn A o' pl S c u) : CommitIn A o' pl c u := h.1

/-- What a commit read keeps once it has stored the tag: the Message-ID's under the configuration's key. -/
def TagIn (A : Word) (cfg : Config) (o' : Nat) (pl : Bytes) (S : Nat) (c : Commit) (u : PancakeState σ) : Prop :=
  HeadIn A o' pl S c u ∧ u.memory (at_ A (S + slotTag)) = (SipHash.tag cfg.key c.messageId).toBitVec

theorem TagIn.head {A : Word} {cfg : Config} {o' : Nat} {pl : Bytes} {S : Nat} {c : Commit} {u : PancakeState σ}
    (h : TagIn A cfg o' pl S c u) : HeadIn A o' pl S c u := h.1

/-- The words of the first `g` groups in slot `S`: each one's place in the configuration and article number. -/
def GroupsIn (A : Word) (cfg : Config) (S : Nat) (c : Commit) (g : Nat) (u : PancakeState σ) : Prop :=
  ∀ g' (hg' : g' < c.groups.length), g' < g → u.memory (at_ A (S + slotGroups + g' * 8)) =
    (BitVec.ofNat 64 (groupIx cfg c.groups[g'].name) <<< 32) ||| .ofNat 64 c.groups[g'].number

/-- The first group the configuration lacks, once the first `g` of the commit are read. -/
def unkUpTo (cfg : Config) (r : RSt) (c : Commit) (g : Nat) : Option Bytes :=
  r.unknown <|> unkFirst cfg (c.groups.take g)

/-- The locals the loop over the groups keeps. -/
def groupVals (A : Word) (S : Nat) (c : Commit) : List (String × Value) :=
  [("rwp", at_ A (rScan + ScanProg.sWindow)), ("rgc", BitVec.ofNat 64 c.groups.length), ("rsl", at_ A S)]

/-- **The loop over the groups**, `g` of them done. -/
def GroupsAt (A : Word) (cfg : Config) (J : Bytes) (r1 : RSt) (s0 : PancakeState σ) (ws : Nat → Word)
    (os : List (Nat × Word)) (l : List (String × Value)) (o' : Nat) (pl : Bytes) (c : Commit) (g : Nat)
    (u : PancakeState σ) : Prop :=
  Mid A cfg J r1 s0 (upd ws rUnknown (bw (unkUpTo cfg r1 c g).isSome)) os l u ∧
    ScanRun.Vals u (("rg", .ofNat 64 g) :: groupVals A (slotAt r1.commits.length) c) ∧
    (TagIn A cfg o' pl (slotAt r1.commits.length) c u ∧ GroupsIn A cfg (slotAt r1.commits.length) c g u ∧
      UnkNoted A r1 (unkUpTo cfg r1 c g) u ∧ g ≤ c.groups.length)

theorem groupsAt_clock {A : Word} {cfg : Config} {J : Bytes} {r1 : RSt} {s0 : PancakeState σ} {ws : Nat → Word}
    {os : List (Nat × Word)} {l : List (String × Value)} {o' : Nat} {pl : Bytes} {c : Commit} (g : Nat) :
    Safe.ClockFree (GroupsAt A cfg J r1 s0 ws os l o' pl c g) := fun s k ⟨h1, h2, h3⟩ => ⟨mid_clock s k h1, h2, h3⟩

/-- The scanner's slots of a commit's groups. -/
theorem commitAt_slots {A : Word} {o' : Nat} {pl : Bytes} {c : Commit} {u : PancakeState σ}
    (h : CommitAt A o' pl c u) : ∀ g (hg : g < c.groups.length), SlotAt A o' pl g c.groups[g] u := h.2.2.2.2.1

/-- What a commit read keeps where a word below the scanner's area is stored. -/
theorem tagIn_stW {A : Word} (hA : A.toNat % 8 = 0) {cfg : Config} {o' : Nat} {pl : Bytes} {c : Commit}
    (hgc : c.groups.length ≤ ScanProg.groupsMax) (hid : c.messageId.length ≤ 250)
    (hfit : o' + 13 + pl.length ≤ ScanProg.windowMax) {S : Nat} (hS : rSlots ≤ S ∧ S + slotSize ≤ RecoverProg.size)
    (u : PancakeState σ) (x : Nat) (v : Word) (hq : TagIn A cfg o' pl S c u) (hx : x < rScan) :
    TagIn A cfg o' pl S c (stW u A x v) := by
  have hn := nums
  obtain ⟨⟨hcf, ⟨hw1, hw2, hw3⟩, hb⟩, ht⟩ := hq
  have hw : ∀ y, rSlots ≤ y → y < RecoverProg.size → ∀ w, u.memory (at_ A y) = w →
      (stW u A x v).memory (at_ A y) = w :=
    fun y hy1 hy2 w e => by rw [stW_word (by omega) (by omega) (by omega)]; exact e
  exact ⟨⟨commitIn_stW hA hcf hgc hfit (.inl hx) (by omega) v, ⟨hw _ (by omega) (by omega) _ hw1,
    hw _ (by omega) (by simp only [slotSizes]; omega) _ hw2, hw _ (by omega) (by simp only [slotMisc]; omega) _ hw3⟩,
    bytesAt_stW hA hb (by omega) (by omega) (fun j hj => by omega) v⟩, hw _ (by omega) (by omega) _ ht⟩

/-- The groups' words kept where a word below the scanner's area is stored. -/
theorem groupsIn_stW {A : Word} {cfg : Config} {c : Commit} (hgc : c.groups.length ≤ ScanProg.groupsMax) {S : Nat}
    (hS : rSlots ≤ S ∧ S + slotSize ≤ RecoverProg.size) {g : Nat} (u : PancakeState σ) (x : Nat) (v : Word)
    (hw : GroupsIn A cfg S c g u) (hx : x < rScan) : GroupsIn A cfg S c g (stW u A x v) := fun g' hg' hlt => by
  have hn := nums
  have := Nat.mul_le_mul_right 8 (show g' ≤ 15 by omega)
  show (stW u A x v).memory _ = _; rw [stW_word (by omega) (by omega) (by omega)]; exact hw g' hg' hlt

/-- The first group the configuration lacks kept where a word past its name is stored. -/
theorem unkNoted_stW {A : Word} (hA : A.toNat % 8 = 0) {r : RSt} {unk : Option Bytes} (u : PancakeState σ) (x : Nat)
    (v : Word) (hf : UnkNoted A r unk u) (hx : rTorn ≤ x) (hx64 : x < 2 ^ 64) : UnkNoted A r unk (stW u A x v) :=
  fun y hy hr => by
    have hn := nums
    obtain ⟨e1, e2, e3⟩ := hf y hy hr
    exact ⟨by show (stW u A x v).memory _ = _; rw [stW_word hx64 (by omega) (by omega)]; exact e1, e2,
      bytesAt_stW hA e3 hx64 (by omega) (fun j hj => by omega) v⟩

/-- **A group of a commit read**: its place in the configuration and article number into the slot, the first the
configuration lacks noted. -/
theorem groupNote_frag (o : Oracle σ) {fail : List Syntax.PStmt} (hfl : LowKK fail) (hfd : declared fail = [])
    {A : Word} {cfg : Config} {J : Bytes} {r1 : RSt} {s0 : PancakeState σ} (h : PBase A s0) {ws : Nat → Word}
    {os : List (Nat × Word)} {l : List (String × Value)} (hgn : ws rGroupCount = .ofNat 64 cfg.groups.length)
    (hos : ∀ q ∈ os, rScan ≤ q.1 ∧ q.1 < rSlots) (hl : ScanRun.Outside crNames l = true) {o' : Nat} {pl : Bytes}
    {c : Commit} (hok : c.ok = true) (hfit : o' + 13 + pl.length ≤ ScanProg.windowMax)
    (hi : r1.commits.length < capacity) (hcnt : cfg.groups.length ≤ groupsMax)
    (hshort : ∀ g (hg : g < cfg.groups.length), cfg.groups[g].length ≤ groupNameMax) {g : Nat}
    (hg : g < c.groups.length) :
    Frag o (groupNote fail) (GroupsAt A cfg J r1 s0 ws os l o' pl c g)
      (GroupsAt A cfg J r1 s0 ws os l o' pl c (g + 1)) := by
  have hn := nums
  have hs := snums
  obtain ⟨-, hid1, hid, hgc, hgr, -, -, -⟩ := ok_bounds hok
  have hsl := slotAt_le hi
  have hal := slotAt_aligned r1.commits.length
  have hSb : rSlots ≤ slotAt r1.commits.length ∧ slotAt r1.commits.length + slotSize ≤ RecoverProg.size := hsl
  obtain ⟨hn1, hn64, hnum⟩ := hgr c.groups[g] (List.getElem_mem hg)
  let name := c.groups[g].name
  let wsg := upd ws rUnknown (bw (unkUpTo cfg r1 c g).isSome)
  let BF (u : PancakeState σ) : Prop :=
    TagIn A cfg o' pl (slotAt r1.commits.length) c u ∧ GroupsIn A cfg (slotAt r1.commits.length) c g u
  have hBFs : ∀ u y v, BF u → BF (setL u y v) := fun _ _ _ h => h
  have hBFc : Safe.ClockFree BF := fun _ _ h => h
  let GA (u : PancakeState σ) : Prop := ∃ s, u.locals "rga" = some (.ofNat 64 (o' + 13 + s)) ∧
    name = (pl.drop s).take name.length ∧ s + name.length ≤ pl.length
  have hslot : ∀ u : PancakeState σ, TagIn A cfg o' pl (slotAt r1.commits.length) c u →
      SlotAt (at_ A rScan) o' pl g c.groups[g] u := fun u hq => commitAt_slots hq.head.commit.at' g hg
  have hdomw : ∀ (ws' : Nat → Word) u, Mid A cfg J r1 s0 ws' os l u → ∀ x, x % 8 = 0 → x < RecoverProg.size →
      u.memaddrs (at_ A x) = true := fun _ u hu x h8 hx => by
    have := h.dom x hx
    rw [hu.kept.memaddrs]; simp only [at_] at this ⊢
    rwa [byteAlign_of_aligned h.hA (X := x) h8] at this
  -- the group's slot in the scanner's area
  let VA := ("rgs", at_ A (rScan + (ScanProg.sGroups + 24 * g))) :: ("rg", BitVec.ofNat 64 g) ::
    groupVals A (slotAt r1.commits.length) c
  refine frag_append (xs := [_]) (M := fun u => Mid A cfg J r1 s0 wsg os l u ∧ ScanRun.Vals u VA ∧
    (BF u ∧ UnkNoted A r1 (unkUpTo cfg r1 c g) u)) (frag_conseq (mid_put o h (y := "rgs") (cr_step _ (by decide))
      (ScanRun.fresh_of_outside hl (by decide))
      (E := .op .add (.op .add (.var "jsc") (.const (.ofNat 64 ScanProg.sGroups)))
        (.mul (.var "rg") (.const (.ofNat 64 ScanProg.groupSlot)))) rfl
      (F := fun u => ScanRun.Vals u (("rg", BitVec.ofNat 64 g) :: groupVals A (slotAt r1.commits.length) c) ∧
        (BF u ∧ UnkNoted A r1 (unkUpTo cfg r1 c g) u))
      (F' := fun u => ScanRun.Vals u VA ∧ (BF u ∧ UnkNoted A r1 (unkUpTo cfg r1 c g) u)) (fun _ _ h => h)
      fun u hu ⟨hvs, hb⟩ => ⟨at_ A (rScan + (ScanProg.sGroups + 24 * g)), by
        simp only [eval, jsc_kept h hu.kept, vals_lookup hvs (lookup_head _ _ _)]
        rw [← BitVec.ofNat_mul, BitVec.add_assoc, ← BitVec.ofNat_add, at_add, Nat.mul_comm g]; rfl,
        ScanRun.vals_cons hvs (by simp [ScanRun.Fresh, groupVals]) _, hb⟩)
    (fun u ⟨hu, hvs, hq, hgw, huf, _⟩ => ⟨hu, hvs, ⟨hq, hgw⟩, huf⟩) fun _ h => h) ?_
  -- where its name lies in the window, its length
  let X (u : PancakeState σ) : Prop := (BF u ∧ UnkNoted A r1 (unkUpTo cfg r1 c g) u) ∧ GA u
  have hXc : Safe.ClockFree X := fun _ _ h => h
  have hags : (rScan + (ScanProg.sGroups + 24 * g)) % 8 = 0 := by omega
  refine frag_append (xs := [_]) (mid_put o h (y := "rga") (cr_step _ (by decide))
    (ScanRun.fresh_of_outside hl (by decide)) (E := .loadWord (.var "rgs")) rfl
    (F := fun u => ScanRun.Vals u VA ∧ (BF u ∧ UnkNoted A r1 (unkUpTo cfg r1 c g) u))
    (F' := fun u => ScanRun.Vals u VA ∧ X u) (fun _ _ h => h) fun u hu ⟨hvs, hb⟩ => by
      obtain ⟨s', f1, _, _, f4, f5⟩ := hslot u hb.1.1
      rw [at_at] at f1
      refine ⟨.ofNat 64 (o' + 13 + s'), ?_, vals_setL hvs (by simp [ScanRun.Fresh, VA, groupVals]) _,
        hb, s', by simp [setL, setLocal], f4, f5⟩
      simp only [eval, vals_lookup hvs (lookup_head _ _ _)]
      rw [if_pos (hdomw _ u hu _ hags (by omega))]
      exact congrArg some f1) ?_
  refine frag_append (xs := [_]) (ScanRun.kept_skip o hfl hfd (by decide)
    (P := fun u => Mid A cfg J r1 s0 wsg os l u ∧ ScanRun.Vals u VA ∧ X u)
    (fun s k ⟨h1, h2, h3⟩ => ⟨mid_clock s k h1, h2, h3⟩)
    fun u ⟨_, _, _, s', hs1, _, hs3⟩ => ⟨o' + 13 + s', hs1, by omega⟩) ?_
  let VB := ("rgl", BitVec.ofNat 64 name.length) :: VA
  refine frag_append (xs := [_]) (mid_put o h (y := "rgl") (cr_step _ (by decide))
    (ScanRun.fresh_of_outside hl (by decide)) (E := .loadWord (.op .add (.var "rgs") (.const (.ofNat 64 8)))) rfl
    (F := fun u => ScanRun.Vals u VA ∧ X u) (F' := fun u => ScanRun.Vals u VB ∧ X u) (fun _ _ h => h)
    fun u hu ⟨hvs, hx⟩ => by
      obtain ⟨s', _, f2, _, _, _⟩ := hslot u hx.1.1.1
      rw [at_at] at f2
      refine ⟨.ofNat 64 name.length, ?_, ScanRun.vals_cons hvs (by simp [ScanRun.Fresh, VA, groupVals]) _,
        hx.1, hx.2.elim fun s'' ⟨h1, h2, h3⟩ => ⟨s'', by simp [setL, setLocal, h1], h2, h3⟩⟩
      simp only [eval, vals_lookup hvs (lookup_head _ _ _)]
      rw [at_add, Nat.add_assoc, if_pos (hdomw _ u hu _ (by omega) (by omega))]
      exact congrArg some f2) ?_
  refine frag_append (xs := [_]) (ScanRun.kept_skip o hfl hfd (by decide)
    (P := fun u => Mid A cfg J r1 s0 wsg os l u ∧ ScanRun.Vals u VB ∧ X u)
    (fun s k ⟨h1, h2, h3⟩ => ⟨mid_clock s k h1, h2, h3⟩)
    fun u ⟨_, hvs, _⟩ => ⟨name.length, vals_lookup hvs (lookup_head _ _ _), hn64⟩) ?_
  -- the configuration searched for the name
  have hXs : ∀ y, y ≠ "rga" → ∀ u v, X u → X (setL u y v) := fun y hya u v hx =>
    ⟨hx.1, hx.2.elim fun s' ⟨h1, h2, h3⟩ => ⟨s', by simp [setL, setLocal, hya.symm, h1], h2, h3⟩⟩
  have put' := fun vs y e E val hy (hya : y ≠ "rga") hyv he hv =>
    crPut_frag o h hl (ws := wsg) (os := os) (r := r1) (s0 := s0) (cfg := cfg) (J := J) vs X y e E val hy hyv he
      (hXs y hya) hXc hv
  refine frag_append (xs := [_]) (put' VB "rx" _ (.op .add (.var "jz") (.const (.ofNat 64 groupsMax)))
    (.ofNat 64 groupsMax) (by decide) (by decide) (by simp [ScanRun.Fresh, VB, VA, groupVals]) rfl
    fun u hu _ _ => by simp [eval, jz_kept h hu.kept]) ?_
  refine frag_append (xs := [_]) (put' _ "rc" _ (.op .add (.var "jz") (.const (.ofNat 64 0)))
    (.ofNat 64 0) (by decide) (by decide) (by simp [ScanRun.Fresh, VB, VA, groupVals]) rfl
    fun u hu _ _ => by simp [eval, jz_kept h hu.kept]) ?_
  refine frag_append (xs := [_]) (put' _ "rgn" _ (rwE rGroupCount) (.ofNat 64 cfg.groups.length) (by decide)
    (by decide) (by simp [ScanRun.Fresh, VB, VA, groupVals]) (rw_lower (by decide)) fun u hu _ _ => by
      rw [mid_rw h hu (by decide) (rw_lower (by decide))]
      show some (ws rGroupCount) = _
      rw [hgn]) ?_
  refine frag_append (xs := [_]) (frag_if o (C := .cmp .less (.const (.ofNat 64 groupsMax)) (.var "rgn")) rfl
    (lowK_any _ (k := .skip) (c := _) rfl) (fun k => ⟨k, rfl⟩) rfl rfl
    (fun s k ⟨h1, h2, h3⟩ => ⟨mid_clock s k h1, h2, h3⟩) (b := false) (fun u ⟨_, hvs, _⟩ => by
      rw [FramerCode.eval_lt (t := u) (a := .const _) (b := .var "rgn") (x := groupsMax) (y := cfg.groups.length)
        (by decide) (by omega) rfl (vals_lookup hvs (lookup_head _ _ _))]
      have e : decide (groupsMax < cfg.groups.length) = false := by
        simp only [decide_eq_false_iff_not]; omega
      rw [e])
    (fun e => absurd e (by decide)) fun _ => frag_nil o fun _ h => h) ?_
  let vsS := ("rgn", BitVec.ofNat 64 cfg.groups.length) :: VB
  have hBn : ∀ u, TagIn A cfg o' pl (slotAt r1.commits.length) c u → GA u → ∃ w, u.locals "rga" = some w ∧
      ∀ j (hj : j < name.length),
      memLoadByte u.memory u.memaddrs u.be (at_ A (rScan + ScanProg.sWindow) + w + BitVec.ofNat 64 j) =
        some name[j] := fun u hq ⟨s', hs1, hs2, hs3⟩ => ⟨_, hs1, fun j hj => by
    have hpl := hq.head.commit.payload (s' + j) (by omega)
    rw [show rScan + ScanProg.sWindow + o' + 13 + (s' + j) = rScan + ScanProg.sWindow + (o' + 13 + s') + j by omega,
      ← at_add, ← at_add] at hpl
    rw [hpl]
    have e : name[j] = ((pl.drop s').take name.length)[j]'(by simp; omega) := List.getElem_of_eq hs2 hj
    rw [e]; simp⟩
  refine frag_append (xs := [_]) (frag_conseq (search_frag o h (outside_sub hl (by decide)) (name := name)
    (show c.groups[g].name.length ≤ 64 from hn64) hcnt hshort (vs := vsS) (by simp [ScanRun.Outside, vsS, VB,
        VA, groupVals]) rfl rfl rfl
    (G := X) hXc (fun u y v hy hx => ⟨hx.1, hx.2.elim fun s' ⟨h1, h2, h3⟩ => ⟨s', by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl <;> simp [setL, setLocal, h1], h2, h3⟩⟩)
      fun u hx => hBn u hx.1.1.1 hx.2)
    (fun u ⟨hu, hvs, hx⟩ => ⟨hu, ScanRun.vals_sub hvs fun q hq => by
      simp only [List.mem_cons, vsS] at hq ⊢
      rcases hq with rfl | rfl | hq
      · exact .inr (.inl rfl)
      · exact .inr (.inr (.inl rfl))
      · rcases hq with rfl | hq
        · exact .inl rfl
        · exact .inr (.inr (.inr hq)), hx⟩) fun _ h => h) ?_
  -- the first group the configuration lacks, noted
  let ix := ixUpTo cfg name cfg.groups.length
  let VS2 := ("rc", BitVec.ofNat 64 cfg.groups.length) :: ("rx", BitVec.ofNat 64 ix) :: vsS
  let G2 (u : PancakeState σ) : Prop := BF u ∧ GA u
  have hG2w : ∀ (u : PancakeState σ) (x : Nat) (v : Word), G2 u → rUnknown ≤ x → x < rTorn → G2 (stW u A x v) :=
    fun u x v ⟨⟨hq, hgw⟩, hga⟩ h1 h2 => ⟨⟨tagIn_stW h.hA hgc hid hfit hSb u x v hq (by omega),
      groupsIn_stW hgc hSb u x v hgw (by omega)⟩, hga⟩
  let unk' := unkUpTo cfg r1 c g <|> if ix = groupsMax then some name else none
  refine frag_append (xs := [_]) (M := fun u => Mid A cfg J r1 s0 (upd wsg rUnknown (bw unk'.isSome)) os l u ∧
    ScanRun.Vals u VS2 ∧ G2 u ∧ UnkNoted A r1 unk' u)
    (frag_conseq (unknownNote_frag o h (ScanRun.fresh_of_outside hl (by decide)) hos (name := name) hn64
      (pw := at_ A (rScan + ScanProg.sWindow)) (ix := ix) (vs := VS2)
      (by simp [ScanRun.Fresh, VS2, vsS, VB, VA, groupVals]) rfl rfl rfl (ix_lt cfg name hcnt)
      (unk := unkUpTo cfg r1 c g)
      (by simp [wsg, upd]) (fun x hx => by show (r1.unknown <|> _) = _; rw [hx]; rfl) (G := G2)
      (fun _ _ h => h) (fun _ _ h => h) hG2w
      (fun u z b hg hz1 hz2 => by rw [putByte_stW h.hA]; exact hG2w u _ _ hg (by omega) (by omega))
      fun u ⟨hb, hga⟩ => hBn u hb.1 hga)
      (fun u ⟨hu, hvs, ⟨hb, huf⟩, hga⟩ => ⟨hu, hvs, ⟨hb, hga⟩, huf⟩) fun _ h => h) ?_
  -- the group's word in the slot: its place in the configuration and its article number
  have hix : ix = groupIx cfg name := by rw [groupIx_eq, Nat.min_eq_left hcnt]
  have hoff : slotGroups + g * 8 < slotSize := by
    have := Nat.mul_le_mul_right 8 (show g ≤ 15 by omega); omega
  refine frag_append (xs := [_]) (slot_store o h hi hos (off := slotGroups + g * 8) (by omega) hoff
    (D := .op .add (.op .add (.var "rsl") (.const (.ofNat 64 slotGroups))) (.mul (.var "rg") (.const
        (.ofNat 64 8))))
    (E := .op .or_ (.shiftL (.var "rx") (.const (.ofNat 64 32)))
      (.loadWord (.op .add (.var "rgs") (.const (.ofNat 64 16))))) rfl rfl
    (val := (BitVec.ofNat 64 (groupIx cfg c.groups[g].name) <<< 32) ||| .ofNat 64 c.groups[g].number)
    (F := fun u => ScanRun.Vals u VS2 ∧ (G2 u ∧ UnkNoted A r1 unk' u))
    (F' := fun u => ScanRun.Vals u VS2 ∧ (TagIn A cfg o' pl (slotAt r1.commits.length) c u ∧
      GroupsIn A cfg (slotAt r1.commits.length) c (g + 1) u ∧ UnkNoted A r1 unk' u)) (fun _ _ h => h)
    (fun u hu ⟨hvs, ⟨⟨hq, _⟩, _⟩, _⟩ => ⟨by
      simp only [eval, vals_lookup hvs (x := "rsl") rfl, vals_lookup hvs (x := "rg") rfl]
      rw [← BitVec.ofNat_mul, BitVec.add_assoc, ← BitVec.ofNat_add, at_add], by
      obtain ⟨_, _, _, f3, _, _⟩ := hslot u hq
      rw [at_at] at f3
      have hw : eval u (.loadWord (.op .add (.var "rgs") (.const (.ofNat 64 16)))) =
          some (.ofNat 64 c.groups[g].number) := by
        simp only [eval, vals_lookup hvs (x := "rgs") rfl]
        rw [at_add, Nat.add_assoc, if_pos (hdomw _ u hu _ (by omega) (by omega))]
        exact congrArg some f3
      rw [eval_or (eval_shl (ev_var (vals_lookup hvs (x := "rx") rfl)) (show 32 < 64 by decide)) hw, hix]⟩)
    fun u _ ⟨hvs, ⟨⟨hq, hgw⟩, _⟩, huf⟩ => ⟨hvs, ?_, ?_, unkNoted_stW h.hA u _ _ huf (by omega) (by omega)⟩) ?_
  · -- what the slot held is kept
    obtain ⟨⟨hcf, ⟨hw1, hw2, hw3⟩, hb⟩, ht⟩ := hq
    have hx : rSlots ≤ (slotAt r1.commits.length) + (slotGroups + g * 8) := Nat.le_trans hsl.1 (Nat.le_add_right _ _)
    have hg8 : g * 8 ≤ 15 * 8 := Nat.mul_le_mul_right 8 (by omega)
    have hlo : ∀ k, k < slotGroups → slotAt r1.commits.length + k ≠ slotAt r1.commits.length + (slotGroups + g * 8) :=
      fun k hk => Nat.ne_of_lt (Nat.add_lt_add_left (Nat.lt_of_lt_of_le hk (Nat.le_add_right _ _)) _)
    have hx64 : slotAt r1.commits.length + (slotGroups + g * 8) < 2 ^ 64 := by omega
    have hS64 : slotAt r1.commits.length + slotTag < 2 ^ 64 := by omega
    refine ⟨⟨commitIn_slots h.hA hgc hfit hx (by omega) hcf, ⟨?_, ?_, ?_⟩, bytesAt_stW h.hA hb (by omega) (by omega)
      (fun j hj => by omega) _⟩, ?_⟩
    · show (stW u A _ _).memory _ = _; rw [stW_word hx64 (by omega) (hlo _ (by decide))]; exact hw1
    · show (stW u A _ _).memory _ = _; rw [stW_word hx64 (by omega) (hlo _ (by decide))]; exact hw2
    · show (stW u A _ _).memory _ = _; rw [stW_word hx64 (by omega) (hlo _ (by decide))]; exact hw3
    · have hne : slotAt r1.commits.length + slotTag ≠ slotAt r1.commits.length + (slotGroups + g * 8) :=
        Nat.ne_of_gt (Nat.add_lt_add_left (show slotGroups + g * 8 < slotTag by
          show 24 + g * 8 < 152; omega) _)
      show (stW u A _ _).memory _ = _; rw [stW_word hx64 hS64 hne]; exact ht
  · -- this group's word, and the others'
    intro g' hg' hlt
    show (stW u A _ _).memory _ = _
    by_cases e : g' = g
    · subst e; rw [Nat.add_assoc]
      show (if _ then _ else _) = _
      rw [if_pos rfl]
    · have := Nat.mul_le_mul_right 8 (show g' ≤ 15 by omega)
      rw [stW_word (by omega) (by omega) (by omega)]; exact hgw g' hg' (by omega)
  -- the next group
  have hU : unk' = unkUpTo cfg r1 c (g + 1) := by
    have hy : (if ix = groupsMax then some name else none) =
        (if cfg.groups.contains name then none else some name) := by
      by_cases hc : cfg.groups.contains name = true
      · rw [if_pos hc, if_neg]; intro e; have := (ix_none hcnt name).mp e; rw [hc] at this; cases this
      · rw [if_neg hc, if_pos ((ix_none hcnt name).mpr (by simpa using hc))]
    show (unkUpTo cfg r1 c g <|> if ix = groupsMax then some name else none) =
      (r1.unknown <|> unkFirst cfg (c.groups.take (g + 1)))
    rw [List.take_succ_eq_append_getElem hg, unkFirst_snoc, hy]
    show ((r1.unknown <|> unkFirst cfg (c.groups.take g)) <|> _) = _
    cases r1.unknown <;> rfl
  exact frag_conseq (mid_put o h (y := "rg") (cr_step _ (by decide)) (ScanRun.fresh_of_outside hl (by decide))
    (E := .op .add (.var "rg") (.const (.ofNat 64 1))) rfl
    (F := fun u => ScanRun.Vals u (("rg", BitVec.ofNat 64 g) :: groupVals A (slotAt r1.commits.length) c) ∧
      (TagIn A cfg o' pl (slotAt r1.commits.length) c u ∧ GroupsIn A cfg (slotAt r1.commits.length) c (g + 1) u ∧
        UnkNoted A r1 unk' u))
    (F' := fun u => ScanRun.Vals u (("rg", BitVec.ofNat 64 (g + 1)) :: groupVals A (slotAt r1.commits.length) c) ∧
      (TagIn A cfg o' pl (slotAt r1.commits.length) c u ∧ GroupsIn A cfg (slotAt r1.commits.length) c (g + 1) u ∧
        UnkNoted A r1 unk' u)) (fun _ _ h => h)
    fun u _ ⟨hvs, hz⟩ => ⟨.ofNat 64 (g + 1), by
      simp only [eval, vals_lookup hvs (lookup_head _ _ _)]; rw [BitVec.ofNat_add],
      vals_head hvs (by simp [ScanRun.Fresh, groupVals]) _, hz⟩)
    (fun u ⟨hu, hvs, hz⟩ => ⟨hu, ScanRun.vals_sub hvs fun q hq => by
      simp only [List.mem_cons, VS2, vsS, VB, VA, groupVals, List.not_mem_nil, or_false] at hq ⊢
      rcases hq with rfl | rfl | rfl | rfl <;> simp, hz⟩)
    fun u ⟨hu, hvs, hq, hgw, huf⟩ => ⟨mid_ws hu (fun x _ => by
      show upd wsg rUnknown _ x = upd ws rUnknown _ x
      simp only [upd]
      by_cases hx : x = rUnknown
      · rw [if_pos hx, if_pos hx, hU]
      · rw [if_neg hx, if_neg hx]; show upd ws rUnknown _ x = _; simp only [upd, if_neg hx]),
      hvs, hq, hgw, by rw [← hU]; exact huf, by omega⟩

/-- The locals a commit read has set once it hashes the Message-ID. -/
def headVals (A : Word) (o' : Nat) (c : Commit) (S : Nat) (n : Value) : List (String × Value) :=
  [("n", .ofNat 64 c.messageId.length), ("p", at_ A (rScan + ScanProg.sWindow + (o' + 13 + 9))), ("k", at_ A rKey),
   ("rj", .ofNat 64 c.messageId.length), ("rwp", at_ A (rScan + ScanProg.sWindow)), ("rio", .ofNat 64 (o' + 13 + 9)),
   ("ril", .ofNat 64 c.messageId.length), ("rgc", .ofNat 64 c.groups.length), ("rsl", at_ A S), ("rcm", n)]

/-- **A commit's head in its slot**: its number, sizes, CRC and lengths, its Message-ID, and the tag's inputs set. -/
theorem slotHead_frag (o : Oracle σ) {fail : List Syntax.PStmt} (hfl : LowKK fail) (hfd : declared fail = [])
    {A : Word} {cfg : Config} {J : Bytes} {r1 : RSt} {s0 : PancakeState σ} (h : PBase A s0) {ws : Nat → Word}
    {os : List (Nat × Word)} {l : List (String × Value)} (hos : ∀ q ∈ os, rScan ≤ q.1 ∧ q.1 < rSlots)
    (hl : ScanRun.Outside crNames l = true) {o' : Nat} {pl : Bytes} {c : Commit} (hok : c.ok = true)
    (hdec : decodeCommit pl = some c) (hfit : o' + 13 + pl.length ≤ ScanProg.windowMax)
    (hi : r1.commits.length < capacity) (n : Value) :
    Frag o (slotHead fail)
      (fun u => Mid A cfg J r1 s0 ws os l u ∧ ScanRun.Vals u [("rsl", at_ A (slotAt r1.commits.length)), ("rcm", n)] ∧
        CommitIn A o' pl c u)
      (fun u => Mid A cfg J r1 s0 ws os l u ∧ ScanRun.Vals u (headVals A o' c (slotAt r1.commits.length) n) ∧
        HeadIn A o' pl (slotAt r1.commits.length) c u) := by
  have hn := nums
  have hs := snums
  obtain ⟨-, hid1, hid, hgc, -, -, -, -⟩ := ok_bounds hok
  obtain ⟨s1, s2⟩ := slotAt_le hi
  have hal := slotAt_aligned r1.commits.length
  have hfr : o' ≤ 17763 := by omega
  let S := slotAt r1.commits.length
  let M := Mid A cfg J r1 s0 ws os l
  have hsw : ∀ x, x % 8 = 0 → x < 1000 → ∀ u, M u → eval u (swE x) = some (u.memory (at_ A (rScan + x))) :=
    fun x h8 hx u hu => mid_sw h hu h8 (by omega)
  have put := crPut_frag o h hl (ws := ws) (os := os) (r := r1) (s0 := s0) (cfg := cfg) (J := J)
  let V1 : List (String × Value) := [("rsl", at_ A S), ("rcm", n)]
  -- its number, sizes
  let W1 (u : PancakeState σ) : Prop := u.memory (at_ A (S + slotSeq)) = .ofNat 64 c.seq
  refine frag_append (xs := [_]) (slot_store o h hi hos (off := slotSeq) (by decide) (by decide)
    (D := .var "rsl") (E := swE ScanProg.sSeq) rfl (sw_lower _) (val := .ofNat 64 c.seq)
    (F := fun u => ScanRun.Vals u V1 ∧ CommitIn A o' pl c u)
    (F' := fun u => ScanRun.Vals u V1 ∧ CommitIn A o' pl c u ∧ W1 u) (fun _ _ h => h)
    (fun u hu ⟨hvs, hf⟩ => ⟨by simp only [eval]; rw [vals_lookup hvs (x := "rsl") rfl]; rfl, by
      rw [hsw _ (by decide) (by decide) u hu]
      have := hf.1.1; rw [at_at] at this; rw [this]⟩)
    fun u _ ⟨hvs, hf⟩ => ⟨hvs, commitIn_slots h.hA hgc hfit (by omega) (by simp only [slotSeq]; omega) hf, by
      show (stW u A (S + slotSeq) _).memory _ = _; simp [stW]⟩) ?_
  let wSizes : Word := (BitVec.ofNat 64 c.headerSize <<< 32) ||| .ofNat 64 c.fileSize
  let W2 (u : PancakeState σ) : Prop := W1 u ∧ u.memory (at_ A (S + slotSizes)) = wSizes
  have hrsl : ∀ (u : PancakeState σ) (vs : List (String × Value)), vs.lookup "rsl" = some (at_ A S) →
      ScanRun.Vals u vs →
      ∀ k, eval u (.op .add (.var "rsl") (.const (.ofNat 64 k))) = some (at_ A (S + k)) :=
    fun u vs hl hvs k => by simp only [eval, vals_lookup hvs hl, at_add]
  refine frag_append (xs := [_]) (slot_store o h hi hos (off := slotSizes) (by decide) (by decide)
    (D := .op .add (.var "rsl") (.const (.ofNat 64 slotSizes)))
    (E := .op .or_ (.shiftL (swE ScanProg.sHeader) (.const (.ofNat 64 32))) (swE ScanProg.sFileSize)) rfl
    (by simp [sw_lower, Lower.lowerExp, Syntax.eOr, Syntax.n]) (val := wSizes)
    (F := fun u => ScanRun.Vals u V1 ∧ CommitIn A o' pl c u ∧ W1 u)
    (F' := fun u => ScanRun.Vals u V1 ∧ CommitIn A o' pl c u ∧ W2 u) (fun _ _ h => h)
    (fun u hu ⟨hvs, hf, _⟩ => ⟨hrsl u V1 rfl hvs slotSizes, by
      have h1 := commitAt_header hf.1; have h2 := commitAt_fileSize hf.1
      rw [at_at] at h1 h2
      have a1 := hsw ScanProg.sHeader (by decide) (by decide) u hu
      have a2 := hsw ScanProg.sFileSize (by decide) (by decide) u hu
      rw [h1] at a1; rw [h2] at a2
      rw [eval_or (eval_shl a1 (show 32 < 64 by decide)) a2]⟩)
    fun u _ ⟨hvs, hf, hw1⟩ => ⟨hvs, commitIn_slots h.hA hgc hfit (by omega) (by simp only [slotSizes]; omega) hf,
      by show (stW u A (S + slotSizes) _).memory _ = _; rw [stW_word (by omega) (by omega) (by simp [slotSeq,
          slotSizes])]; exact hw1,
      by show (stW u A (S + slotSizes) _).memory _ = _; simp [stW]⟩) ?_
  -- the count of groups, the Message-ID's length and place, checked in range
  have hQc : ∀ (vs : List (String × Value)) (Q : Assn σ), Safe.ClockFree Q →
      Safe.ClockFree (fun u => M u ∧ ScanRun.Vals u vs ∧ Q u) := fun _ _ hQ s k ⟨h1, h2, h3⟩ =>
    ⟨mid_clock s k h1, h2, hQ s k h3⟩
  let Q2 (u : PancakeState σ) : Prop := CommitIn A o' pl c u ∧ W2 u
  have hcw : ∀ (u : PancakeState σ) (x : Nat) (w : Word), u.memory (at_ (at_ A rScan) x) = w →
      u.memory (at_ A (rScan + x)) = w := fun u x w hw => by rw [← at_at]; exact hw
  let V2 := ("rgc", BitVec.ofNat 64 c.groups.length) :: V1
  refine frag_append (xs := [_]) (put V1 Q2 "rgc" _ (swE ScanProg.sGroupCount) _ (by decide)
    (by simp [ScanRun.Fresh, V1]) (sw_lower _) (fun _ _ h => h) (fun _ _ h => h)
    fun u hu _ hq => by rw [hsw _ (by decide) (by decide) u hu, hcw u _ _ (commitAt_count hq.1.1)]) ?_
  refine frag_append (xs := [_]) (ScanRun.kept_skip o hfl hfd (by decide) (hQc V2 Q2 fun _ _ h => h)
    fun u ⟨_, hvs, _⟩ => ⟨_, vals_lookup hvs rfl, hgc⟩) ?_
  let V3 := ("ril", BitVec.ofNat 64 c.messageId.length) :: V2
  refine frag_append (xs := [_]) (put V2 Q2 "ril" _ (swE ScanProg.sIdLen) _ (by decide)
    (by simp [ScanRun.Fresh, V2, V1]) (sw_lower _) (fun _ _ h => h) (fun _ _ h => h)
    fun u hu _ hq => by rw [hsw _ (by decide) (by decide) u hu, hcw u _ _ (commitAt_idLen hq.1.1)]) ?_
  refine frag_append (xs := [_]) (ScanRun.kept_skip o hfl hfd (by decide) (hQc V3 Q2 fun _ _ h => h)
    fun u ⟨_, hvs, _⟩ => ⟨_, vals_lookup hvs rfl, hid⟩) ?_
  let V4 := ("rio", BitVec.ofNat 64 (o' + 13 + 9)) :: V3
  refine frag_append (xs := [_]) (put V3 Q2 "rio" _ (swE ScanProg.sIdAt) _ (by decide)
    (by simp [ScanRun.Fresh, V3, V2, V1]) (sw_lower _) (fun _ _ h => h) (fun _ _ h => h)
    fun u hu _ hq => by rw [hsw _ (by decide) (by decide) u hu, hcw u _ _ (commitAt_idAt hq.1.1)]) ?_
  refine frag_append (xs := [_]) (ScanRun.kept_skip o hfl hfd (by decide) (hQc V4 Q2 fun _ _ h => h)
    fun u ⟨_, hvs, _⟩ => ⟨_, vals_lookup hvs rfl, by omega⟩) ?_
  let V5 := ("rwp", at_ A (rScan + ScanProg.sWindow)) :: V4
  refine frag_append (xs := [_]) (put V4 Q2 "rwp" _ (.op .add (.var "jsc") (.const (.ofNat 64 ScanProg.sWindow)))
    (at_ A (rScan + ScanProg.sWindow)) (by decide) (by simp [ScanRun.Fresh, V4, V3, V2, V1]) rfl (fun _ _ h => h)
        (fun _ _ h => h)
    fun u hu _ _ => by simp only [eval, jsc_kept h hu.kept, at_add]) ?_
  -- the CRC, the Message-ID's length and the count of groups
  let wMisc : Word := ((BitVec.ofNat 64 c.fileCrc <<< 16) ||| (BitVec.ofNat 64 c.messageId.length <<< 8)) |||
    .ofNat 64 c.groups.length
  let W3 (u : PancakeState σ) : Prop := W2 u ∧ u.memory (at_ A (S + slotMisc)) = wMisc
  let Q3 (u : PancakeState σ) : Prop := CommitIn A o' pl c u ∧ W3 u
  refine frag_append (xs := [_]) (slot_store o h hi hos (off := slotMisc) (by decide) (by decide)
    (D := .op .add (.var "rsl") (.const (.ofNat 64 slotMisc)))
    (E := .op .or_ (.op .or_ (.shiftL (swE ScanProg.sCrc) (.const (.ofNat 64 16)))
      (.shiftL (.var "ril") (.const (.ofNat 64 8)))) (.var "rgc")) rfl
    (by simp [sw_lower, Lower.lowerExp, Syntax.eOr, Syntax.n, Syntax.v]) (val := wMisc)
    (F := fun u => ScanRun.Vals u V5 ∧ Q2 u) (F' := fun u => ScanRun.Vals u V5 ∧ Q3 u) (fun _ _ h => h)
    (fun u hu ⟨hvs, hf, _⟩ => ⟨hrsl u V5 rfl hvs slotMisc, by
      have a1 := hsw ScanProg.sCrc (by decide) (by decide) u hu
      rw [hcw u _ _ (commitAt_crc hf.1)] at a1
      rw [eval_or (eval_or (eval_shl a1 (show 16 < 64 by decide))
        (eval_shl (ev_var (vals_lookup hvs (x := "ril") rfl)) (show 8 < 64 by decide)))
        (ev_var (vals_lookup hvs (x := "rgc") rfl))]⟩)
    fun u _ ⟨hvs, hf, hw1, hw2⟩ => ⟨hvs, commitIn_slots h.hA hgc hfit (by omega) (by simp only [slotMisc]; omega) hf,
      ⟨by show (stW u A (S + slotMisc) _).memory _ = _; rw [stW_word (by omega) (by omega) (by simp [slotSeq,
          slotMisc])]; exact hw1,
       by show (stW u A (S + slotMisc) _).memory _ = _; rw [stW_word (by omega) (by omega) (by simp [slotSizes,
           slotMisc])]; exact hw2⟩,
      by show (stW u A (S + slotMisc) _).memory _ = _; simp [stW]⟩) ?_
  refine frag_append (xs := [_]) (put V5 Q3 "rj" _ (.op .add (.var "jz") (.const (.ofNat 64 0))) 0 (by decide)
    (by simp [ScanRun.Fresh, V5, V4, V3, V2, V1]) rfl (fun _ _ h => h) (fun _ _ h => h)
    fun u hu _ _ => by simp [eval, jz_kept h hu.kept]) ?_
  -- the Message-ID copied into the slot
  have bump := crBump_frag o h hl (ws := ws) (os := os) (r := r1) (s0 := s0) (cfg := cfg) (J := J)
  obtain ⟨hidv, hid9⟩ := ScanRun.id_octets hdec
  have hidget : ∀ j (hj : j < c.messageId.length), c.messageId[j] = pl[9 + j]'(by omega) := fun j hj => by
    have : c.messageId[j] = ((pl.drop 9).take c.messageId.length)[j]'(by simp; omega) := by
      congr 1
    rw [this, List.getElem_take, List.getElem_drop]
  let I (j : Nat) : Assn σ := fun u => M u ∧ ScanRun.Vals u (("rj", .ofNat 64 j) :: V5) ∧
    (Q3 u ∧ BytesAt A (S + slotId) (c.messageId.take j) u ∧ j ≤ c.messageId.length)
  have hIc : ∀ j, Safe.ClockFree (I j) := fun _ s k ⟨h1, h2, h3⟩ => ⟨mid_clock s k h1, h2, h3⟩
  have hbody : ∀ j, decide (j < c.messageId.length) = true → Frag o
      [.storeb (Syntax.eAdd (Syntax.atOff (Syntax.v "rsl") slotId) (Syntax.v "rj"))
        (.loadb (Syntax.eAdd (Syntax.eAdd (Syntax.v "rwp") (Syntax.v "rio")) (Syntax.v "rj"))), ScanProg.inc "rj"]
      (I j) (I (j + 1)) := fun j hj => by
    simp only [decide_eq_true_eq] at hj
    have hoff : slotId + j < slotSize := by omega
    refine frag_append (xs := [_]) (slot_storeb o h hi hos (off := slotId + j) hoff
      (D := .op .add (.op .add (.var "rsl") (.const (.ofNat 64 slotId))) (.var "rj"))
      (E := .loadByte (.op .add (.op .add (.var "rwp") (.var "rio")) (.var "rj"))) rfl rfl (b := c.messageId[j])
      (F := fun u => ScanRun.Vals u (("rj", .ofNat 64 j) :: V5) ∧
        (Q3 u ∧ BytesAt A (S + slotId) (c.messageId.take j) u ∧ j ≤ c.messageId.length))
      (F' := fun u => ScanRun.Vals u (("rj", .ofNat 64 j) :: V5) ∧
        (Q3 u ∧ BytesAt A (S + slotId) (c.messageId.take (j + 1)) u ∧ j + 1 ≤ c.messageId.length))
      (fun _ _ h => h) (fun u _ ⟨hvs, hq, _, _⟩ => ⟨by
        simp only [eval, vals_lookup hvs (x := "rsl") rfl, vals_lookup hvs (x := "rj") rfl, at_add, Nat.add_assoc]
        rfl, by
        have hm := hq.1.2 (9 + j) (by omega)
        rw [show rScan + ScanProg.sWindow + o' + 13 + (9 + j) = rScan + ScanProg.sWindow + (o' + 13 + 9) + j by omega]
          at hm
        simp only [eval, vals_lookup hvs (x := "rwp") rfl, vals_lookup hvs (x := "rio") rfl,
          vals_lookup hvs (x := "rj") rfl, at_add, hm, hidget j hj]⟩) fun u hu ⟨hvs, hq, hb, _⟩ => ⟨hvs, ?_, ?_,
              by omega⟩) ?_
    · -- what is kept
      obtain ⟨hcf, ⟨hw1, hw2⟩, hw3⟩ := hq
      have hz : (S + (slotId + j)) / 8 * 8 ≠ S + slotSeq ∧ (S + (slotId + j)) / 8 * 8 ≠ S + slotSizes ∧
          (S + (slotId + j)) / 8 * 8 ≠ S + slotMisc := by
        simp only [slotSeq, slotSizes, slotMisc, slotId]; omega
      refine ⟨commitIn_put h.hA hcf hgc hfit (.inr (by omega)) (by omega) _, ⟨?_, ?_⟩, ?_⟩ <;> rw [putByte_stW h.hA]
      · show (stW u A _ _).memory (at_ A (S + slotSeq)) = _
        rw [stW_word (by omega) (by omega) (Ne.symm hz.1)]; exact hw1
      · show (stW u A _ _).memory (at_ A (S + slotSizes)) = _
        rw [stW_word (by omega) (by omega) (Ne.symm hz.2.1)]; exact hw2
      · show (stW u A _ _).memory (at_ A (S + slotMisc)) = _
        rw [stW_word (by omega) (by omega) (Ne.symm hz.2.2)]; exact hw3
    · -- one more octet of the Message-ID
      have hl : (c.messageId.take j).length = j := by simp; omega
      have := bytesAt_snoc (A := A) (z := S + slotId) hb (by rw [hl]; omega) (by
        rw [hl, hu.kept.memaddrs]; exact h.dom _ (by omega)) c.messageId[j]
      rw [hl, Nat.add_assoc] at this
      rwa [List.take_succ_eq_append_getElem hj]
    · exact bump "rj" V5 _ j (by decide) (by simp [ScanRun.Fresh, V5, V4, V3, V2, V1]) (fun _ _ h => h)
        (fun _ _ h => h)
  refine frag_append (xs := [_]) (M := I c.messageId.length) (frag_conseq (frag_count o
    (c := Syntax.eLt (Syntax.v "rj") (Syntax.v "ril")) (C := .cmp .less (.var "rj") (.var "ril")) rfl
    (lowK_any _ (k := .skip) (c := _) rfl) hIc (fun j => noDecl (P' := I j) _ rfl)
    (g := fun j => decide (j < c.messageId.length)) (fun j u ⟨_, hvs, _, _, _⟩ => by
      rw [FramerCode.eval_lt (t := u) (a := .var "rj") (b := .var "ril") (x := j) (y := c.messageId.length)
        (by omega) (by omega) (vals_lookup hvs (lookup_head _ _ _)) (vals_lookup hvs rfl)]; rfl) hbody 0)
    (fun u ⟨hu, hvs, hq⟩ => ⟨hu, hvs, hq, fun i hi => absurd hi (by simp), Nat.zero_le _⟩)
    fun u ⟨j, ⟨hu, hvs, hq, hb, hjl⟩, hg⟩ => by
      have : j = c.messageId.length := by simp only [decide_eq_false_iff_not] at hg; omega
      subst this; exact ⟨hu, hvs, hq, hb, Nat.le_refl _⟩) ?_
  -- the tag, under the configuration's key
  let V6 := ("rj", BitVec.ofNat 64 c.messageId.length) :: V5
  let Q4 (u : PancakeState σ) : Prop := Q3 u ∧ BytesAt A (S + slotId) c.messageId u
  refine frag_conseq (P0 := fun u => M u ∧ ScanRun.Vals u V6 ∧ Q4 u) ?_
    (fun u ⟨hu, hvs, hq, hb, _⟩ => ⟨hu, hvs, hq, by rwa [List.take_length] at hb⟩) fun _ h => h
  let V7 := ("k", at_ A rKey) :: V6
  refine frag_append (xs := [_]) (put V6 Q4 "k" _ (.op .add (.var "rsc") (.const (.ofNat 64 rKey))) (at_ A rKey)
    (by decide) (by simp [ScanRun.Fresh, V6, V5, V4, V3, V2, V1]) rfl (fun _ _ h => h) (fun _ _ h => h)
    fun u hu _ _ => by simp only [eval, rsc_kept h hu.kept]; rfl) ?_
  let pv := at_ A (rScan + ScanProg.sWindow + (o' + 13 + 9))
  let V8 := ("p", pv) :: V7
  refine frag_append (xs := [_]) (put V7 Q4 "p" _ (.op .add (.var "rwp") (.var "rio")) pv
    (by decide) (by simp [ScanRun.Fresh, V7, V6, V5, V4, V3, V2, V1]) rfl (fun _ _ h => h) (fun _ _ h => h)
    fun u _ hvs _ => by
      simp only [eval, vals_lookup hvs (x := "rwp") rfl, vals_lookup hvs (x := "rio") rfl, at_add]; rfl) ?_
  exact frag_conseq (put V8 Q4 "n" (Syntax.v "ril") (.var "ril") _ (by decide)
    (by simp [ScanRun.Fresh, V8, V7, V6, V5, V4, V3, V2, V1]) rfl (fun _ _ h => h) (fun _ _ h => h)
    fun u _ hvs _ => vals_lookup hvs rfl) (fun _ h => h)
    fun u ⟨hu, hvs, ⟨hcf, ⟨hw1, hw2⟩, hw3⟩, hb⟩ => ⟨hu, hvs, hcf, ⟨hw1, hw2, hw3⟩, hb⟩

/-- A commit's Message-ID hashed under the configuration's key. -/
theorem slotSip_frag (o : Oracle σ) {A : Word} {cfg : Config} {J : Bytes} {r1 : RSt} {s0 : PancakeState σ}
    (h : PBase A s0) {ws : Nat → Word} {os : List (Nat × Word)} {l : List (String × Value)}
    (hl : ScanRun.Outside crNames l = true) {o' : Nat} {pl : Bytes} {c : Commit} (hok : c.ok = true)
    (hdec : decodeCommit pl = some c) (n : Value) :
    Frag o SipProg.sipSrc
      (fun u => Mid A cfg J r1 s0 ws os l u ∧ ScanRun.Vals u (headVals A o' c (slotAt r1.commits.length) n) ∧
        HeadIn A o' pl (slotAt r1.commits.length) c u)
      (fun u => (Mid A cfg J r1 s0 ws os l u ∧ ScanRun.Vals u (headVals A o' c (slotAt r1.commits.length) n) ∧
        HeadIn A o' pl (slotAt r1.commits.length) c u) ∧
          u.locals "r" = some (SipHash.tag cfg.key c.messageId).toBitVec) := by
  obtain ⟨-, hid1, hid, -, -, -, -, -⟩ := ok_bounds hok
  let S := slotAt r1.commits.length
  let M := Mid A cfg J r1 s0 ws os l
  obtain ⟨hidv, hid9⟩ := ScanRun.id_octets hdec
  have hidget : ∀ j (hj : j < c.messageId.length), c.messageId[j] = pl[9 + j]'(by omega) := fun j hj => by
    have : c.messageId[j] = ((pl.drop 9).take c.messageId.length)[j]'(by simp; omega) := by
      congr 1
    rw [this, List.getElem_take, List.getElem_drop]
  let V9 := headVals A o' c S n
  let pv := at_ A (rScan + ScanProg.sWindow + (o' + 13 + 9))
  have hsipl : ScanRun.Outside ScanRun.sipNames l = true := by
    simp only [ScanRun.Outside, List.all_eq_true] at hl ⊢
    intro q hq; have := hl q hq
    simp only [crNames, List.contains_append, Bool.not_or, Bool.and_eq_true] at this; exact this.2
  have hsipv : ScanRun.Outside ScanRun.sipNames V9 = true := by
    simp [ScanRun.Outside, V9, headVals, ScanRun.sipNames]
  refine frag_conseq (ScanRun.sip_frag o (kv := at_ A rKey) (pv := pv)
    (key := cfg.key) (msg := c.messageId) (by omega) (G := fun u => M u ∧ ScanRun.Vals u V9 ∧ HeadIn A o' pl S c u)
    (fun u u' ⟨hu, hvs, hq⟩ hk => by
      have hv' := ScanRun.vals_kept hvs hk hsipv
      have hm' := mid_locals hu (fun y hy => cr_step y (by simp [crNames, hy])) hsipl hk
      rw [kept_false_eq hk] at hv' hm' ⊢
      exact ⟨hm', hv', hq⟩)
    (fun s k ⟨h1, h2, h3⟩ => ⟨mid_clock s k h1, h2, h3⟩)) (fun u ⟨hu, hvs, hq⟩ => ⟨?_, hu, hvs, hq⟩)
    fun _ h => h
  · -- the hash's inputs: the key's sixteen octets, the Message-ID in the window
    have hkey : readByteArray u.memory u.memaddrs u.be (at_ A rKey) 16 = some cfg.key := by
      have := read_of_bytes cfg.key (at_ A rKey) (fun i hi => by rw [at_add]; exact hu.rest.config.key i hi)
      rwa [hu.rest.config.keyLen] at this
    have hmsg : readByteArray u.memory u.memaddrs u.be pv c.messageId.length = some c.messageId :=
      read_of_bytes c.messageId pv fun i hi => by
        have hm := hq.commit.payload (9 + i) (by omega)
        rw [show rScan + ScanProg.sWindow + o' + 13 + (9 + i) = rScan + ScanProg.sWindow + (o' + 13 + 9) + i by omega]
          at hm
        rw [at_add, hm, hidget i hi]
    have hb : ∀ y, y ∈ RecoverProg.locals → ∃ x, u.locals y = some x := fun y hy => kept_has hu.kept (h.bound y hy)
    exact ⟨⟨vals_lookup hvs rfl, vals_lookup hvs rfl, vals_lookup hvs rfl, hb "r" (by decide), hkey, hmsg⟩,
      fun y hy => hb y (by revert y; decide)⟩

/-- A commit's tag stored in its slot. -/
theorem slotTag_frag (o : Oracle σ) {A : Word} {cfg : Config} {J : Bytes} {r1 : RSt} {s0 : PancakeState σ}
    (h : PBase A s0)
    {ws : Nat → Word} {os : List (Nat × Word)} {l : List (String × Value)}
    (hos : ∀ q ∈ os, rScan ≤ q.1 ∧ q.1 < rSlots) {o' : Nat} {pl : Bytes} {c : Commit} (hok : c.ok = true)
    (hfit : o' + 13 + pl.length ≤ ScanProg.windowMax) (hi : r1.commits.length < capacity) (n : Value) :
    Frag o [.store (Syntax.atOff (Syntax.v "rsl") slotTag) (Syntax.v "r")]
      (fun u => (Mid A cfg J r1 s0 ws os l u ∧ ScanRun.Vals u (headVals A o' c (slotAt r1.commits.length) n) ∧
        HeadIn A o' pl (slotAt r1.commits.length) c u) ∧
          u.locals "r" = some (SipHash.tag cfg.key c.messageId).toBitVec)
      (fun u => Mid A cfg J r1 s0 ws os l u ∧ ScanRun.Vals u (headVals A o' c (slotAt r1.commits.length) n) ∧
        TagIn A cfg o' pl (slotAt r1.commits.length) c u) := by
  have hn := nums
  obtain ⟨-, hid1, hid, hgc, -, -, -, -⟩ := ok_bounds hok
  obtain ⟨s1, s2⟩ := slotAt_le hi
  have hal := slotAt_aligned r1.commits.length
  let S := slotAt r1.commits.length
  have hrsl : ∀ (u : PancakeState σ) (vs : List (String × Value)), vs.lookup "rsl" = some (at_ A S) →
      ScanRun.Vals u vs →
      ∀ k, eval u (.op .add (.var "rsl") (.const (.ofNat 64 k))) = some (at_ A (S + k)) :=
    fun u vs hl hvs k => by simp only [eval, vals_lookup hvs hl, at_add]
  let V9 := headVals A o' c S n
  -- the tag stored
  let wTag : Word := (SipHash.tag cfg.key c.messageId).toBitVec
  have hSal : S % 8 = 0 := hal
  refine frag_conseq (slot_store o h hi hos (off := slotTag) (by decide) (by decide)
    (D := .op .add (.var "rsl") (.const (.ofNat 64 slotTag))) (E := .var "r") rfl rfl (val := wTag)
    (F := fun u => (ScanRun.Vals u V9 ∧ HeadIn A o' pl S c u) ∧ u.locals "r" = some wTag)
    (F' := fun u => ScanRun.Vals u V9 ∧ TagIn A cfg o' pl S c u) (fun _ _ h => h)
    (fun u _ ⟨⟨hvs, _⟩, hr⟩ => ⟨hrsl u V9 rfl hvs slotTag, hr⟩) fun u _ hf => ?_)
    (fun u ⟨⟨hu, hvs, hq⟩, hr⟩ => ⟨hu, ⟨hvs, hq⟩, hr⟩) fun _ h => h
  · obtain ⟨⟨hvs, hcf, ⟨hw1, hw2, hw3⟩, hb⟩, _⟩ := hf
    have hn1 : S + slotSeq ≠ S + slotTag := by omega
    have hn2 : S + slotSizes ≠ S + slotTag := by omega
    have hn3 : S + slotMisc ≠ S + slotTag := by omega
    refine ⟨hvs, ⟨commitIn_slots h.hA hgc hfit (by omega) (by simp only [slotTag]; omega) hcf, ⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩
    · show (stW u A (S + slotTag) _).memory _ = _; rw [stW_word (by omega) (by omega) hn1]; exact hw1
    · show (stW u A (S + slotTag) _).memory _ = _; rw [stW_word (by omega) (by omega) hn2]; exact hw2
    · show (stW u A (S + slotTag) _).memory _ = _; rw [stW_word (by omega) (by omega) hn3]; exact hw3
    · exact bytesAt_stW h.hA hb (by omega) (by simp only [slotId]; omega)
        (fun j hj => by simp only [slotId, slotTag]; omega) _
    · show (stW u A (S + slotTag) _).memory _ = _; simp [stW, wTag]

/-- **A commit read**, as `recordRead` notes it: counted, and while the index has room, in its slot, the first group
the configuration lacks noted. -/
theorem commitRead_frag (o : Oracle σ) {fail : List Syntax.PStmt} (hfl : LowKK fail) (hfd : declared fail = [])
    {A : Word} {cfg : Config} {J : Bytes} {r1 : RSt} {s0 : PancakeState σ} (h : PBase A s0) (hp1 : r1.phase = 3)
    {ws : Nat → Word} {os : List (Nat × Word)} {l : List (String × Value)}
    (hws : ∀ x ∈ scalarOffs, ws x = scalars cfg r1 x) (hos : ∀ q ∈ os, rScan ≤ q.1 ∧ q.1 < rSlots)
    (hrgo : l.lookup "rgo" = some 1) (hl : ScanRun.Outside crNames l = true) {o' : Nat} {pl : Bytes} {c : Commit}
    (hok : c.ok = true) (hdec : decodeCommit pl = some c) (hfit : o' + 13 + pl.length ≤ ScanProg.windowMax)
    (hcm : r1.commits.length < 2 ^ 62) :
    Frag o (commitRead fail) (fun u => Mid A cfg J r1 s0 ws os l u ∧ CommitIn A o' pl c u)
      (POut A cfg J s0 (RecoverSpec.recordRead cfg r1 (.commit c), none)) := by
  have hn := nums
  obtain ⟨-, -, hid, hgc, -, -, -, -⟩ := ok_bounds hok
  have hcfc : ∀ x ∈ scalarOffs, ∀ (u : PancakeState σ) (v : Word), CommitIn A o' pl c u →
      CommitIn A o' pl c (stW u A x v) :=
    fun x hx u v hu => by
    have := (free_scalar x hx).1; simp only [Free] at this
    exact commitIn_stW h.hA hu hgc hfit (by omega) (by omega) v
  -- the count
  refine frag_append (xs := [_]) (mid_put o h (y := "rcm") (by decide) (ScanRun.fresh_of_outside hl (by decide))
    (E := .op .add (rwE rCommits) (.const (.ofNat 64 1))) rfl (F := CommitIn A o' pl c)
    (F' := fun u => CommitIn A o' pl c u ∧ u.locals "rcm" = some (.ofNat 64 (r1.commits.length + 1))) (fun _ _ h => h)
    fun u hu hf => ⟨.ofNat 64 (r1.commits.length + 1), by
      simp only [eval, mid_rw h hu (x := rCommits) (by decide) (rw_lower (by decide))]
      rw [hws rCommits (by decide), show scalars cfg r1 rCommits = .ofNat 64 r1.commits.length from rfl,
        BitVec.ofNat_add], hf, by simp [setL, setLocal]⟩) ?_
  refine frag_append (xs := [_]) (mid_set_and o h (x := rCommits) (by decide) (E := .var "rcm") rfl
    (val := .ofNat 64 (r1.commits.length + 1)) (fun _ _ hf => hf.2) (fun _ _ h => h)
    fun u v hf => ⟨hcfc _ (by decide) u v hf.1, hf.2⟩) ?_
  -- a slot while the index has room
  refine frag_if o (C := .op .and_ (.cmp .less (.const (.ofNat 64 0)) (.var "rcm"))
    (.cmp .notLess (.const (.ofNat 64 capacity)) (.var "rcm"))) rfl ?_ (fun k => ⟨k, rfl⟩) rfl rfl pout_clock
    (b := decide (r1.commits.length + 1 ≤ capacity)) (fun u ⟨_, _, hrcm⟩ => by
      refine (FramerCode.eval_and (FramerCode.eval_lt (t := u) (a := .const _) (b := .var "rcm") (x := 0)
        (y := r1.commits.length + 1) (by decide) (by omega) rfl hrcm) (FramerCode.eval_le (t := u) (a := .var "rcm")
          (b := .const _) (x := r1.commits.length + 1) (y := capacity) (by omega) (by decide) hrcm rfl)).trans ?_
      simp) (fun hc => ?_) fun hc => ?_
  rotate_right
  · -- no room: counted only
    simp only [decide_eq_false_iff_not] at hc
    rw [recordRead_commit, if_neg hc]
    exact frag_nil o fun u ⟨hu, _, _⟩ => mid_end hu (offs_all (by
      and_intros <;> first
        | exact (hws _ (by decide)).trans rfl
        | (show BitVec.ofNat 64 (r1.commits.length + 1) = BitVec.ofNat 64 (r1.commits ++ [c]).length
           rw [List.length_append, List.length_singleton])))
      (fun hr => ⟨hr.seq, hr.nameLen, hr.name, hr.unknown, hr.config, hr.scan, fun j hj hjc => by
        have hj' : j < r1.commits.length := by simp at hj; omega
        rw [List.getElem_append_left hj']; exact hr.slots j hj' hjc, fun h5 => by dsimp only at h5; omega⟩)
      (vals_lookup hu.vals hrgo)
  · exact lowKK_append (xs := [_]) (lowK_any _ (k := .skip) (c := _) rfl) (lowKK_slotNote hfl)
  · -- room: the commit in its slot
    have hc' : r1.commits.length + 1 ≤ capacity := by simp only [decide_eq_true_eq] at hc; exact hc
    have hi : r1.commits.length < capacity := by omega
    obtain ⟨-, -⟩ := slotAt_le hi
    let S := slotAt r1.commits.length
    let ws1 := upd ws rCommits (.ofNat 64 (r1.commits.length + 1))
    let M := Mid A cfg J r1 s0 ws1 os l
    -- the slot's address
    simp only [List.append_assoc]
    refine frag_conseq (P0 := fun u => M u ∧ ScanRun.Vals u [("rcm", .ofNat 64 (r1.commits.length + 1))] ∧
      CommitIn A o' pl c u) ?_ (fun u ⟨hu, hf, hrcm⟩ => ⟨hu, fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact hrcm, hf⟩) fun _ h => h
    have put := crPut_frag o h hl (ws := ws1) (os := os) (r := r1) (s0 := s0) (cfg := cfg) (J := J)
    -- the slot's address
    refine frag_append (xs := [_]) (put _ (CommitIn A o' pl c) "rsl" _
      (.op .add (.op .add (.var "rsc") (.const (.ofNat 64 rSlots)))
        (.mul (.op .sub (.var "rcm") (.const (.ofNat 64 1))) (.const (.ofNat 64 slotSize)))) (at_ A S)
      (by decide) (by simp [ScanRun.Fresh]) rfl (fun _ _ h => h) (fun _ _ h => h) fun u hu hvs _ => by
        simp only [eval, rsc_kept h hu.kept, vals_lookup hvs (x := "rcm") rfl]
        rw [slot_addr A hi]) ?_
    -- the slot's head, the tag, and the groups
    refine frag_append (slotHead_frag o hfl hfd h hos hl hok hdec hfit hi _) ?_
    refine frag_append (slotSip_frag o h hl hok hdec _) ?_
    refine frag_append (xs := [_]) (slotTag_frag o h hos hok hfit hi _) ?_
    -- the groups: each one's place and number, and the first the configuration lacks
    refine frag_pure (cfg.groups.length ≤ groupsMax ∧
      ∀ g (hg : g < cfg.groups.length), cfg.groups[g].length ≤ groupNameMax)
      (fun u ⟨hu, _⟩ => ⟨hu.rest.config.count, hu.rest.config.short⟩)
      (lowKK_groups hfl) fun ⟨hcnt, hshort⟩ => ?_
    -- none yet
    let V9 := headVals A o' c S (.ofNat 64 (r1.commits.length + 1))
    have hVG : ∀ u : PancakeState σ, ScanRun.Vals u V9 → ScanRun.Vals u (groupVals A S c) := fun u hvs =>
      ScanRun.vals_sub hvs fun q hq => by
        simp only [groupVals, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl <;> simp [V9, headVals]
    have hu0 : unkUpTo cfg r1 c 0 = r1.unknown := by
      show (r1.unknown <|> unkFirst cfg (c.groups.take 0)) = r1.unknown
      cases r1.unknown <;> rfl
    have hws1 : ws1 rUnknown = bw (unkUpTo cfg r1 c 0).isSome := by
      show ws rUnknown = _
      rw [hws rUnknown (by decide), hu0]; rfl
    refine frag_append (xs := [_]) (M := GroupsAt A cfg J r1 s0 ws1 os l o' pl c 0) (frag_conseq (mid_put o h
      (y := "rg") (cr_step _ (by decide))
      (ScanRun.fresh_of_outside hl (by decide)) (e := ScanProg.lit 0)
      (E := .op .add (.var "jz") (.const (.ofNat 64 0))) rfl
      (F := fun u => ScanRun.Vals u V9 ∧ TagIn A cfg o' pl S c u)
      (F' := fun u => ScanRun.Vals u (("rg", .ofNat 64 0) :: groupVals A S c) ∧
        (TagIn A cfg o' pl S c u ∧ GroupsIn A cfg S c 0 u ∧ UnkNoted A r1 (unkUpTo cfg r1 c 0) u ∧ 0 ≤ c.groups.length))
      (fun s k ⟨h1, h2⟩ => ⟨h1, h2⟩) fun u hu ⟨hvs, hq⟩ => by
        refine ⟨0, by simp [eval, jz_kept h hu.kept], ScanRun.vals_cons (hVG u hvs)
          (by simp [ScanRun.Fresh, groupVals]) _, hq, ?_, ?_, Nat.zero_le _⟩
        · intro g' _ hlt; exact absurd hlt (Nat.not_lt_zero _)
        · intro x hx hr; rw [hu0, hr] at hx; cases hx)
      (fun u h => h) fun u ⟨hu, hvs, hq⟩ => ⟨mid_ws hu (upd_same hws1), hvs, hq⟩) ?_
    refine frag_conseq (frag_count o (c := Syntax.eLt (Syntax.v "rg") (Syntax.v "rgc"))
      (C := .cmp .less (.var "rg") (.var "rgc")) rfl (lowKK_groupNote hfl) groupsAt_clock
      (fun g => noDecl (P' := GroupsAt A cfg J r1 s0 ws1 os l o' pl c g) _ rfl)
      (g := fun g => decide (g < c.groups.length)) (fun g u ⟨_, hvs, _, _, _, hg⟩ => by
        rw [FramerCode.eval_lt (t := u) (a := .var "rg") (b := .var "rgc") (x := g) (y := c.groups.length) (by omega)
          (by omega) (vals_lookup hvs (lookup_head _ _ _)) (vals_lookup hvs rfl)]; rfl)
      (fun g hg => groupNote_frag o hfl hfd h (by show ws rGroupCount = _; rw [hws rGroupCount (by decide)]; rfl) hos hl
        hok hfit hi hcnt hshort (of_decide_eq_true hg)) 0) (fun _ h => h) ?_
    -- the commit in its slot, the first group the configuration lacks noted
    intro u ⟨g, ⟨hu, _, hq, hgw, huf, hg⟩, hgg⟩
    have : g = c.groups.length := by simp only [decide_eq_false_iff_not] at hgg; omega
    subst this
    have hunk : unkUpTo cfg r1 c c.groups.length = (r1.unknown <|> RecoverSpec.unknownIn cfg c) := by
      show (r1.unknown <|> unkFirst cfg (c.groups.take c.groups.length)) = _
      rw [List.take_length]; rfl
    rw [recordRead_commit, if_pos hc']
    obtain ⟨⟨-, ⟨hw1, hw2, hw3⟩, hid'⟩, htag⟩ := hq
    refine mid_end hu ?_ (fun hr => ?_) (vals_lookup hu.vals hrgo)
    · refine offs_all ?_
      and_intros <;> first
        | exact (hws _ (by decide)).trans rfl
        | (show BitVec.ofNat 64 (r1.commits.length + 1) = BitVec.ofNat 64 (r1.commits ++ [c]).length
           rw [List.length_append, List.length_singleton])
        | (show bw (unkUpTo cfg r1 c c.groups.length).isSome = _; rw [hunk]; rfl)
    · refine ⟨fun hp => hr.seq hp, hr.nameLen, hr.name, fun x hx => ?_, hr.config, hr.scan, fun j hj hjc => ?_,
        fun h5 => by dsimp only at h5; omega⟩
      · -- the first group the configuration lacks
        cases hr0 : r1.unknown with
        | some y =>
          have : x = y := by dsimp only at hx; rw [hr0] at hx; simp at hx; exact hx.symm
          subst this; exact hr.unknown x hr0
        | none => exact huf x (by rw [hunk]; exact hx) hr0
      · -- the slots: the commits' before, and the new one
        dsimp only at hj
        rw [List.length_append, List.length_singleton] at hj
        by_cases hji : j < r1.commits.length
        · rw [List.getElem_append_left hji]; exact hr.slots j hji hjc
        · have hje : j = r1.commits.length := by omega
          subst hje
          rw [List.getElem_append_right (Nat.le_refl _)]
          simp only [Nat.sub_self, List.getElem_cons_zero]
          exact ⟨hw1, hw2, hw3, htag, hid, hid', hgc, fun g hg => hgw g hg hg⟩

end DN.News.RecoverArea
