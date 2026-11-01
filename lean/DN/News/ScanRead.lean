-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.ScanArea
import DN.News.ScanStep

/-!
# DN.News.ScanRead

If it goes on, the step finds the frame at the next place in the window and checks it (`frame_frag`), reads
the record it holds (`rec_frag`), and takes it, or refuses a second format (`accept_frag`), as `stepSpec`
says through `Journal.next`; what a step leaves (`OutAt`, `StepOut`).
-/

namespace DN.News.ScanRun

open DN.Compiler DN.Compiler.Wp DN.Compiler.Frag DN.Compiler.Bytes DN.News.Journal DN.News.ScanProg
open DN.News.FramerCode (bw bw_ne0 bw_eq0 eval_lt eval_eq eval_and)
open DN.Compiler.WpBytes (eval_addc eval_add eval_load)

variable {σ : Type}

/-! ## The frame read -/

/-- The step's locals that keep their value once the frame is found: the journal's length, the window's
start, where the frame starts, whether the key is read, the window's place, what is left, and the frame's
offset and place in the window. -/
def fixedV (A : Word) (J : Bytes) (st : St) : List (String × Value) :=
  [("jsz", BitVec.ofNat 64 J.length), ("jb", BitVec.ofNat 64 st.base), ("jp", BitVec.ofNat 64 st.pos),
   ("jky", bw st.key.isSome), ("jw", at_ A sWindow), ("jrem", BitVec.ofNat 64 (J.length - st.pos)),
   ("jo", BitVec.ofNat 64 (st.pos - st.base)), ("jf", at_ A (sWindow + (st.pos - st.base)))]

/-- After the frame's check: the area as it was, the fixed locals, and `jwhy` the code of what `fault` finds,
with the payload's length and the type of a frame that checks. -/
structure FwDone (A : Word) (J : Bytes) (st : St) (s0 u : PancakeState σ) : Prop where
  kept : Kept ScanProg.locals (AreaW A) s0 u
  area : AreaAt A J st u
  vals : Vals u (fixedV A J st)
  why : u.locals "jwhy" = some (BitVec.ofNat 64 (codeOf (fault st.key st.pos (J.drop st.pos))))
  len : fault st.key st.pos (J.drop st.pos) = none →
    u.locals "jpl" = some (BitVec.ofNat 64 (readLE ((J.drop st.pos).take 4)))
  type : fault st.key st.pos (J.drop st.pos) = none → u.locals "jt" = some (BitVec.ofNat 64 (typeOf (J.drop st.pos)))

theorem fwNames_locals : ∀ y ∈ fwNames, y ∈ ScanProg.locals := by decide

theorem lowKK_frameWhy (keyed : Bool) : LowKK (ScanProg.frameWhy keyed) :=
  lowKK_append (xs := [_]) (lowK_any _ (k := .skip) (c := _) rfl)
    (lowKK_ite rfl (lowK_any _ (k := .skip) (c := _) rfl) (lowKK_lenPart keyed))

theorem recNames_locals : ∀ y ∈ recNames, y ∈ ScanProg.locals := by decide

/-- **A frame checked where it starts**: at `q`, in the window, under the journal's key once read, or with
`keyed` false the key a frame of the format's shape carries. If it goes on, `jwhy` holds the code of what
`fault` finds, and of a frame that checks `jpl` the payload's length and `jt` the type; `l` still holds. -/
theorem frameCheck_frag (o : Oracle σ) {A : Word} {J : Bytes} {st : St} {s0 : PancakeState σ} (h : StepIn A J st s0)
    (keyed : Bool) {q : Nat} {l : List (String × Value)} (hq : st.base ≤ q) (hqJ : q < J.length)
    (hwin : q + min (J.length - q) maxFrame ≤ st.base + st.len) (hjq : l.lookup "jq" = some (BitVec.ofNat 64 q))
    (hjf : l.lookup "jf" = some (at_ A (sWindow + (q - st.base))))
    (hjr : l.lookup "jr" = some (BitVec.ofNat 64 (J.length - q)))
    (hjky : keyed = false → l.lookup "jky" = some (bw st.key.isSome)) (hkeyed : keyed = true → st.key.isSome = true)
    (hout : Outside fwNames l = true) :
    Frag o (ScanProg.frameWhy keyed) (Ctx A J st s0 l) (fun u => Ctx A J st s0 l u ∧
      u.locals "jwhy" = some (BitVec.ofNat 64 (codeOf (fault st.key q (J.drop q)))) ∧
      (fault st.key q (J.drop q) = none → u.locals "jpl" = some (BitVec.ofNat 64 (readLE ((J.drop q).take 4))) ∧
        u.locals "jt" = some (BitVec.ofNat 64 (typeOf (J.drop q))))) := by
  have hn := nums
  have hJ := h.short
  have hlen := h.valid.len
  refine frag_each o (lowKK_frameWhy keyed) fun s hs => ?_
  have hin : FwIn keyed A st.key q (q - st.base) (J.drop q) s := {
    hA := h.hA
    dom := ctx_dom h hs
    sp := ctx_jsc h hs
    jz := ctx_jz h hs
    jq := vals_lookup hs.vals hjq
    jf := vals_lookup hs.vals hjf
    jr := by rw [List.length_drop]; exact vals_lookup hs.vals hjr
    jky := fun e => vals_lookup hs.vals (hjky e)
    keyed := hkeyed
    key := fun kk hk => hs.area.key kk hk
    bytes := fun i hi hm => by
      simp only [List.length_drop] at hi
      rw [Nat.add_assoc, hs.area.window (q - st.base + i) (by omega), List.getElem_drop,
        show st.base + (q - st.base + i) = q + i by omega, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by omega)]
      rfl
    room := by omega
    q := by omega
    len := by rw [List.length_drop]; omega
    bound := fun y hy => kept_has hs.kept (h.bound y (fwNames_locals y hy)) }
  exact frag_conseq (frameWhy_frag o hin) (fun _ h => h) fun u hu =>
    ⟨⟨kept_trans hs.kept (kept_widen hu.kept fwNames_locals fun _ => msgW_areaW),
      areaAt_msg h.hA hs.area hlen hu.kept, vals_kept hs.vals hu.kept hout⟩, hu.why, fun hf => ⟨hu.len hf, hu.type hf⟩⟩

/-- **The frame at `jp` found and checked**: if it goes on, after the head, the frame's place and length in locals,
`jwhy` the code of what `fault` finds. -/
theorem frame_frag (o : Oracle σ) {A : Word} {J : Bytes} {st : St} {s0 : PancakeState σ} (h : StepIn A J st s0)
    {fail : List Syntax.PStmt} (hfl : LowKK fail) (hfd : declared fail = []) (hpos : st.pos < J.length)
    (hw : ¬ st.base + st.len < st.pos + min (J.length - st.pos) maxFrame) :
    Frag o (ScanProg.frameRead fail) (Hd A J st s0) (FwDone A J st s0) := by
  have hn := nums
  have hv := h.valid
  have hJ := h.short
  have hbp := hv.base
  have hpl := hv.pos
  have hlen := hv.len
  refine frag_conseq (P0 := Ctx A J st s0 (hdV A J st)) ?_ (fun u hu => hd_ctx h hu) fun _ h => h
  have f1 := ctx_assign o h (x := "jq") (e := Syntax.v "jp") (E := .var "jp") rfl (by decide) (l := hdV A J st) rfl
    (v := BitVec.ofNat 64 st.pos) fun u hu => by simp only [eval]; exact vals_lookup hu.vals rfl
  have f2 := frameAt_frag o h hfl hfd (q := st.pos) (l := ("jq", BitVec.ofNat 64 st.pos) :: hdV A J st) hbp
    (by omega) (by omega) rfl rfl rfl rfl rfl rfl
  have f3 := ctx_assign o h (x := "jr") (e := Syntax.v "jrem") (E := .var "jrem") rfl (by decide)
    (l := ("jpp", at_ A (sWindow + (st.pos - st.base) + 13)) :: ("jf", at_ A (sWindow + (st.pos - st.base))) ::
      ("jo", BitVec.ofNat 64 (st.pos - st.base)) :: ("jq", BitVec.ofNat 64 st.pos) :: hdV A J st) rfl
    (v := BitVec.ofNat 64 (J.length - st.pos)) fun u hu => by simp only [eval]; exact vals_lookup hu.vals rfl
  have f4 := frameCheck_frag o h false (q := st.pos) (l := ("jr", BitVec.ofNat 64 (J.length - st.pos)) ::
    ("jpp", at_ A (sWindow + (st.pos - st.base) + 13)) :: ("jf", at_ A (sWindow + (st.pos - st.base))) ::
      ("jo", BitVec.ofNat 64 (st.pos - st.base)) :: ("jq", BitVec.ofNat 64 st.pos) :: hdV A J st) hbp hpos
    (by omega) rfl rfl rfl (fun _ => rfl) (fun e => by cases e) rfl
  refine frag_conseq (frag_append (frag_append (frag_append f1 f2) f3) f4) (fun _ h => h) fun u hu =>
    ⟨hu.1.kept, hu.1.area, fun q hq => ?_, hu.2.1, fun hf => (hu.2.2 hf).1, fun hf => (hu.2.2 hf).2⟩
  simp only [fixedV, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact vals_lookup hu.1.vals rfl

/-! ## The record read -/

/-- The code of why reading stops at a place, zero where it goes on. -/
def whyOf : Next → Nat
  | .bad w => whyCode w
  | _ => 0

/-- After the record's reading: as after the frame's check, `jwhy` the code of why reading stops, zero for a
record; of a record, its type, its payload's length, its payload's place and a commit's fields. -/
structure RcDone (A : Word) (J : Bytes) (st : St) (s0 u : PancakeState σ) : Prop where
  kept : Kept ScanProg.locals (AreaW A) s0 u
  area : AreaAt A J st u
  vals : Vals u (fixedV A J st)
  why : u.locals "jwhy" = some (BitVec.ofNat 64 (whyOf (next spec st.key st.pos (J.drop st.pos))))
  record : ∀ rec taken rest, next spec st.key st.pos (J.drop st.pos) = .record rec taken rest →
    u.locals "jrec" = some (BitVec.ofNat 64 rec.type) ∧ u.locals "jpl" = some (BitVec.ofNat 64 (taken - 14)) ∧
    u.locals "jpp" = some (at_ A (sWindow + (st.pos - st.base) + 13)) ∧
    ∀ c, rec = .commit c → CommitAt A (st.pos - st.base) (payloadOf (J.drop st.pos)) c u

theorem rcDone_clock {A : Word} {J : Bytes} {st : St} {s0 : PancakeState σ} : Safe.ClockFree (RcDone A J st s0) :=
  fun _ _ h => { h with kept := { h.kept with }, area := { h.area with } }

theorem lowKK_recordOf {fail : List Syntax.PStmt} (hfl : LowKK fail) : LowKK (ScanProg.recordOf fail) :=
  lowKK_append (xs := [_, _]) (lowK_any _ (k := .skip) (c := _) rfl)
    (lowKK_append (xs := [_]) (lowKK_ite rfl (lowK_any _ (k := .skip) (c := _) rfl)
      (lowKK_ite rfl (lowKK_decode hfl) (lowK_any _ (k := .skip) (c := _) rfl))) (lowK_any _ (k := .skip) (c := _) rfl))

/-- **The record read**: if it goes on, of a frame that checks, the record's type, its payload's length and
place, and a commit's fields. -/
theorem rec_frag (o : Oracle σ) {A : Word} {J : Bytes} {st : St} {s0 : PancakeState σ} (h : StepIn A J st s0)
    {fail : List Syntax.PStmt} (hfl : LowKK fail) (hfd : declared fail = []) (hpos : st.pos < J.length)
    (hw : ¬ st.base + st.len < st.pos + min (J.length - st.pos) maxFrame) :
    Frag o [ScanProg.recordPart fail] (FwDone A J st s0) (RcDone A J st s0) := by
  have hn := nums
  have hv := h.valid
  have hJ := h.short
  have hbp := hv.base
  have hpl := hv.pos
  have hst := hv.stop
  have hlen := hv.len
  have hbl : (J.drop st.pos).length = J.length - st.pos := List.length_drop
  have hne : J.drop st.pos ≠ [] := fun e => by rw [e] at hbl; simp at hbl; omega
  have hnx := next_fault st.key st.pos hne
  have hev : ∀ u, FwDone A J st s0 u → eval u (.cmp .equal (.var "jwhy") (.const 0)) =
      some (bw (decide (codeOf (fault st.key st.pos (J.drop st.pos)) = 0))) := fun u hu =>
    eval_eq (y := 0) codeOf_lt (by decide) (by simp only [eval]; exact hu.why) rfl
  refine frag_ite o (C := .cmp .equal (.var "jwhy") (.const 0)) rfl rcDone_clock
    (fun u hu => ⟨_, hev u hu⟩) ?_ (noDecl _ rfl) (frag_nil o fun u ⟨hu, h0⟩ => ?_) (noDecl _ rfl)
  · refine frag_pure (fault st.key st.pos (J.drop st.pos) = none) (fun u ⟨hu, hne0⟩ => by
      rw [hev u hu] at hne0; exact codeOf_zero.mp (by simpa using bw_ne0 hne0)) (lowKK_recordOf hfl) fun hf => ?_
    obtain ⟨hfl1, hfl2⟩ := fault_none hf
    have hplen := payload_length hfl1
    simp only [List.length_drop] at hfl1
    refine frag_each o (lowKK_recordOf hfl) fun s ⟨hs, _⟩ => ?_
    have hin : RecIn A (st.pos - st.base) (typeOf (J.drop st.pos)) (payloadOf (J.drop st.pos)) s := {
      hA := h.hA
      dom := kept_dom h hs.kept
      sp := kept_jsc h hs.kept
      jz := kept_jz h hs.kept
      jw := hs.vals ("jw", at_ A sWindow) (by simp [fixedV])
      jo := hs.vals ("jo", BitVec.ofNat 64 (st.pos - st.base)) (by simp [fixedV])
      jf := hs.vals ("jf", at_ A (sWindow + (st.pos - st.base))) (by simp [fixedV])
      jt := hs.type hf
      jpl := by rw [hplen]; exact hs.len hf
      jwhy := by have := hs.why; rw [hf] at this; exact this
      payload := fun i hi => by
        rw [hplen] at hi
        rw [show sWindow + (st.pos - st.base) + 13 + i = sWindow + (st.pos - st.base + 13 + i) by omega,
          hs.area.window _ (by omega), payload_get i (by rw [hplen]; exact hi) (by simp only [List.length_drop]; omega),
          List.getElem_drop, show st.base + (st.pos - st.base + 13 + i) = st.pos + (13 + i) by omega,
          List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
        rfl
      room := by omega
      len := by rw [hplen]; exact hfl2
      ht := (List.getD (J.drop st.pos) 12 0).isLt
      bound := fun y hy => kept_has hs.kept (h.bound y (recNames_locals y hy)) }
    refine frag_conseq (recordOf_frag o hin hfl hfd) (fun _ h => h) fun u hu => ?_
    have hk : Kept ScanProg.locals (AreaW A) s0 u := kept_trans hs.kept
      (kept_widen hu.kept recNames_locals fun _ ⟨x, _, h2, e⟩ => ⟨x, by simp only [ScanProg.size]; omega, e⟩)
    have harea : AreaAt A J st u := areaAt_keep h.hA hs.area hlen hu.kept.memaddrs hu.kept.be
      fun x hx hx8 hr => hu.kept.memory _ (by
        have e := not_field h.hA (x := x) (by simp only [sStatus, sType] at hr ⊢; omega) (by omega)
        rwa [align_at h.hA, show x / 8 * 8 = x by omega] at e)
    have hjpl : u.locals "jpl" = some (BitVec.ofNat 64 (readLE ((J.drop st.pos).take 4))) := by
      rw [hu.kept.locals _ (by decide)]; exact hs.len hf
    refine ⟨hk, harea, vals_kept hs.vals hu.kept (xs := recNames) rfl, ?_, ?_⟩
    · rw [hnx, hf]
      have := hu.why
      cases hr : Journal.recordOf spec (typeOf (J.drop st.pos)) (payloadOf (J.drop st.pos)) with
      | none => rw [hr] at this; simpa [whyOf] using this
      | some r => rw [hr] at this; simpa [whyOf] using this
    · intro r tk rs e
      rw [hnx, hf] at e
      cases hr : Journal.recordOf spec (typeOf (J.drop st.pos)) (payloadOf (J.drop st.pos)) with
      | none => rw [hr] at e; cases e
      | some r' =>
        rw [hr] at e
        simp only [Next.record.injEq] at e
        obtain ⟨rfl, rfl, rfl⟩ := e
        refine ⟨by have := hu.jrec; simpa [recType, hr] using this, by rw [hjpl]; congr 2; simp [headerLength],
          hu.jpp, fun c hc => hu.commit c (by rw [hr, hc])⟩
  · rw [hev u hu] at h0
    have hf := bw_eq0 h0
    simp only [decide_eq_false_iff_not] at hf
    obtain ⟨w, hw'⟩ : ∃ w, fault st.key st.pos (J.drop st.pos) = some w := by
      cases e : fault st.key st.pos (J.drop st.pos) with
      | none => exact absurd (codeOf_zero.mpr e) hf
      | some w => exact ⟨w, rfl⟩
    have hb : next spec st.key st.pos (J.drop st.pos) = .bad w := by rw [hnx, hw']
    refine ⟨hu.kept, hu.area, hu.vals, ?_, fun r tk rs e => by rw [hb] at e; cases e⟩
    rw [hb]
    have := hu.why
    rw [hw'] at this
    exact this

/-! ## What a step leaves -/

/-- **What a step leaves**, as `stepSpec` says: the status, and with it the area's next state and the octets
wanted, the record read and its fields, or where and why reading stops. -/
def OutAt (A : Word) (J : Bytes) (st : St) : Out → PancakeState σ → Prop
  | .clean, u => u.memory (at_ A sStatus) = BitVec.ofNat 64 clean ∧ AreaAt A J st u
  | .want st' n, u => u.memory (at_ A sStatus) = BitVec.ofNat 64 wanted ∧ AreaAt A J st' u ∧
      u.memory (at_ A sWant) = BitVec.ofNat 64 n
  | .record r st', u => u.memory (at_ A sStatus) = BitVec.ofNat 64 ScanProg.record ∧ AreaAt A J st' u ∧
      u.memory (at_ A sType) = BitVec.ofNat 64 r.type ∧
      ∀ c, r = .commit c → CommitAt A (st.pos - st.base) (payloadOf (J.drop st.pos)) c u
  | .stop (.torn p), u => u.memory (at_ A sStatus) = BitVec.ofNat 64 torn ∧ u.memory (at_ A sPos) = BitVec.ofNat 64 p ∧
      AreaAt A J st u ∧ J.length ≤ st.base + st.len
  | .stop (.corrupt p w), u => u.memory (at_ A sStatus) = BitVec.ofNat 64 corrupt ∧
      u.memory (at_ A sPos) = BitVec.ofNat 64 p ∧ u.memory (at_ A sWhy) = BitVec.ofNat 64 (whyCode w) ∧ AreaAt A J st u
  | .stop .clean, _ => False

/-- A step's end: the locals but its own and the memory but the area as they were, and what `stepSpec` says. -/
def StepOut (A : Word) (J : Bytes) (st : St) (s0 u : PancakeState σ) : Prop :=
  Kept ScanProg.locals (AreaW A) s0 u ∧ OutAt A J st (stepSpec J st) u

theorem outAt_clock {A : Word} {J : Bytes} {st : St} : ∀ (r : Out), Safe.ClockFree (OutAt (σ := σ) A J st r)
  | .clean => fun _ _ ⟨h1, h2⟩ => ⟨h1, { h2 with }⟩
  | .want _ _ => fun _ _ ⟨h1, h2, h3⟩ => ⟨h1, { h2 with }, h3⟩
  | .record _ _ => fun _ _ ⟨h1, h2, h3, h4⟩ => ⟨h1, { h2 with }, h3, h4⟩
  | .stop (.torn _) => fun _ _ ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, { h3 with }, h4⟩
  | .stop (.corrupt _ _) => fun _ _ ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, { h4 with }⟩
  | .stop .clean => fun _ _ h => h

theorem stepOut_clock {A : Word} {J : Bytes} {st : St} {s0 : PancakeState σ} : Safe.ClockFree (StepOut A J st s0) :=
  fun c u ⟨h1, h2⟩ => ⟨{ h1 with }, outAt_clock _ c u h2⟩

/-! ## A record accepted -/

/-- The key's words. -/
def KeyW (A : Word) (a : Word) : Prop := ∃ x, sKey ≤ x ∧ x < sMessage ∧ a = at_ A x

/-- **The format's key copied**: sixteen octets of the payload, twenty into it, into the area's key. -/
theorem keyCopy_frag (o : Oracle σ) {A : Word} (hA : A.toNat % 8 = 0) {o' : Nat}
    {kb : List (BitVec 8)} (hkb : kb.length = 16) {F : Assn σ} (hFc : Safe.ClockFree F)
    (hF : ∀ u a b, F u → KeyW A (byteAlign a) → F { u with memory := putByte u.memory u.be a b })
    (hsp : ∀ u, F u → u.locals "jsc" = some A) (hpp : ∀ u, F u → u.locals "jpp" = some (at_ A (sWindow + o' + 13)))
    (hdom : ∀ u, F u → Dom A u.memaddrs)
    (hsrc : ∀ u, F u → ∀ i, i < 16 →
      memLoadByte u.memory u.memaddrs u.be (at_ A (sWindow + o' + 13 + (20 + i))) = some (kb.getD i 0)) :
    Frag o ScanProg.keyCopy F (fun u => F u ∧ readByteArray u.memory u.memaddrs u.be (at_ A sKey) 16 = some kb) := by
  have hn := nums
  let Q (j : Nat) (u : PancakeState σ) : Prop :=
    F u ∧ ∀ i, i < j → memLoadByte u.memory u.memaddrs u.be (at_ A (sKey + i)) = some (kb.getD i 0)
  have hQc : ∀ j, Safe.ClockFree (Q j) := fun _ _ _ ⟨h1, h2⟩ => ⟨hFc _ _ h1, h2⟩
  have step : ∀ j, j ≤ 16 → Frag o ((List.range j).map ScanProg.keyStore) (Q 0) (Q j) := by
    intro j
    induction j with
    | zero => intro _; exact frag_nil o fun _ h => h
    | succ j ih =>
      intro hj
      rw [List.range_succ, List.map_append]
      refine frag_append (ih (by omega))
        (storeb_frag o (D := .op .add (.var "jsc") (.const (BitVec.ofNat 64 (sKey + j))))
        (E := .loadByte (.op .add (.var "jpp") (.const (BitVec.ofNat 64 (magic.length + j)))))
        (by rw [atOff_lower (p := sp) (P := .var "jsc") rfl, if_neg (by omega)])
        (by simp only [byte, Lower.lowerExp, atOff_lower (p := Syntax.v "jpp") (P := .var "jpp") rfl,
          if_neg (show ¬ magic.length + j = 0 by omega)])
        (hQc (j + 1)) fun u ⟨hu, hb⟩ => ?_)
      have hal : byteAlign (at_ A (sKey + j)) = at_ A ((sKey + j) / 8 * 8) := align_at hA _
      have hkw : KeyW A (byteAlign (at_ A (sKey + j))) := ⟨(sKey + j) / 8 * 8, by omega, by omega, hal⟩
      have hdm : u.memaddrs (byteAlign (at_ A (sKey + j))) = true := hdom u hu _ (by simp only [ScanProg.size]; omega)
      have hE : eval u (.loadByte (.op .add (.var "jpp") (.const (BitVec.ofNat 64 (magic.length + j))))) =
          some ((kb.getD j 0).setWidth 64) := by
        have hm : magic.length = 20 := rfl
        simp only [eval, hpp u hu, at_add, hm, hsrc u hu j (by omega)]
      refine ⟨at_ A (sKey + j), _, by simp [eval, hsp u hu, at_], hE, hdm, hF u _ _ hu hkw, fun i hi => ?_⟩
      by_cases hij : i = j
      · subst hij; rw [load_putByte_same _ _ _ _ _ hdm, Bytes.setWidth64_8]
      · rw [load_putByte_diff _ _ _ _ _ _ (at_ne (by omega) (by omega) (by omega))]; exact hb i (by omega)
  refine frag_conseq (step 16 (Nat.le_refl _)) (fun u hu => ⟨hu, fun i hi => absurd hi (Nat.not_lt_zero _)⟩)
    fun u ⟨hu, hb⟩ => ⟨hu, ?_⟩
  have := read_of_bytes (m := u.memory) (dm := u.memaddrs) (be := u.be) kb (at_ A sKey) fun i hi => by
    rw [at_add, hb i (by omega), List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
  rwa [hkb] at this

/-- During `accept`, from `ur`: the locals as they were, the words `ws` stored below the key, the rest of the area
as it was but the key with `kf`, which then holds `kb`. -/
structure AccAt (A : Word) (ur : PancakeState σ) (kf : Bool) (kb : List (BitVec 8)) (ws : List (Nat × Word))
    (u : PancakeState σ) : Prop where
  kept : Kept [] (AreaW A) ur u
  stored : ∀ q ∈ ws, u.memory (at_ A q.1) = q.2
  below : ∀ q ∈ ws, q.1 < sKey
  rest : ∀ x, x < ScanProg.size → x % 8 = 0 → (∀ q ∈ ws, q.1 ≠ x) → (kf = false ∨ x < sKey ∨ sMessage ≤ x) →
    u.memory (at_ A x) = ur.memory (at_ A x)
  key : kf = true → readByteArray u.memory u.memaddrs u.be (at_ A sKey) 16 = some kb

theorem accAt_clock {A : Word} {ur : PancakeState σ} {kf : Bool} {kb : List (BitVec 8)} {ws : List (Nat × Word)} :
    Safe.ClockFree (AccAt A ur kf kb ws) := fun _ _ h => { h with kept := { h.kept with } }

theorem accAt_store {A : Word} (hA : A.toNat % 8 = 0) {ur u : PancakeState σ} {kf : Bool} {kb : List (BitVec 8)}
    {ws : List (Nat × Word)} (h : AccAt A ur kf kb ws u) {x : Nat} (hx : x < sKey) (hx8 : x % 8 = 0)
    (hxw : ∀ q ∈ ws, q.1 ≠ x) (v : Word) :
    AccAt A ur kf kb ((x, v) :: ws) { u with memory := fun k => if k = at_ A x then v else u.memory k } := by
  have hn := nums
  refine ⟨kept_word h.kept ⟨x, by simp only [ScanProg.size]; omega, rfl⟩ v, fun q hq => ?_, fun q hq => ?_,
    fun y hy hy8 hyw hk => ?_, fun hk => ?_⟩
  · simp only [List.mem_cons] at hq
    rcases hq with rfl | hq
    · simp
    · have := h.below q hq
      simp only [if_neg (fun e => hxw q hq (at_inj (by omega) (by omega) e))]
      exact h.stored q hq
  · simp only [List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact hx
    · exact h.below q hq
  · simp only [List.mem_cons, forall_eq_or_imp] at hyw
    simp only [if_neg (fun e => hyw.1 (at_inj (by omega) (by omega) e).symm)]
    exact h.rest y hy hy8 hyw.2 hk
  · rw [← h.key hk]
    refine readByteArray_congr 16 _ fun j hj => ?_
    rw [load_word_ne]
    rw [at_add, align_at hA]
    exact at_ne (by omega) (by omega) (by omega)

/-- What `accept` leaves of a record read: a second format refused, or the record taken. -/
def AccOut (A : Word) (J : Bytes) (st : St) (s0 : PancakeState σ) (rec : Record) (taken : Nat) (u : PancakeState σ) :
    Prop :=
  Kept ScanProg.locals (AreaW A) s0 u ∧ OutAt A J st (if !st.acc.isEmpty && rec.key.isSome then
    .stop (.corrupt st.pos .formatAgain) else
    .record rec { st with pos := st.pos + taken, key := st.key <|> rec.key, acc := rec :: st.acc }) u

theorem lowKK_accept : LowKK ScanProg.accept := lowK_any _ (k := .skip) (c := _) rfl

/-- **The record taken**: if it goes on, a second format refused as corruption, else the record and the area's
next state, as `stepSpec` says. -/
theorem accept_frag (o : Oracle σ) {A : Word} {J : Bytes} {st : St} {s0 : PancakeState σ} (h : StepIn A J st s0)
    (hpos : st.pos < J.length) (hw : ¬ st.base + st.len < st.pos + min (J.length - st.pos) maxFrame) {rec : Record}
    {taken : Nat} {rest : Bytes} (hnx : next spec st.key st.pos (J.drop st.pos) = .record rec taken rest) :
    Frag o ScanProg.accept (RcDone A J st s0) (AccOut A J st s0 rec taken) := by
  have hn := nums
  have hv := h.valid
  have hJ := h.short
  have hbp := hv.base
  have hpl := hv.pos
  have hst := hv.stop
  have hlen := hv.len
  have hcnt := hv.count
  obtain ⟨hf, hro, htk⟩ := next_record_of hnx
  obtain ⟨-, ht1, ht2, ht3⟩ := next_record hnx
  simp only [List.length_drop, headerLength] at ht1 ht2
  obtain ⟨hfl1, hfl2⟩ := fault_none hf
  have hplen := payload_length hfl1
  simp only [List.length_drop] at hfl1
  have hrt : rec.type < 2 ^ 63 := by cases rec <;> simp [Record.type, formatType, commitType, startType]
  refine frag_each o lowKK_accept fun ur hur => ?_
  obtain ⟨hjrec, hjpl, hjpp, hcom⟩ := hur.record rec taken rest hnx
  have hsp := kept_jsc h hur.kept
  have hdom := kept_dom h hur.kept
  have hjp : ur.locals "jp" = some (BitVec.ofNat 64 st.pos) :=
    hur.vals ("jp", BitVec.ofNat 64 st.pos) (by simp [fixedV])
  let kb : List (BitVec 8) := (payloadOf (J.drop st.pos)).drop 20
  let W := fun kf ws => AccAt (σ := σ) A ur kf kb ws
  have hloc : ∀ kf ws u, W kf ws u → ∀ y, u.locals y = ur.locals y := fun _ _ u hu y =>
    hu.kept.locals y (List.not_mem_nil)
  have hmem : ∀ kf ws u, W kf ws u → u.memaddrs = ur.memaddrs ∧ u.be = ur.be := fun _ _ u hu =>
    ⟨hu.kept.memaddrs, hu.kept.be⟩
  have hsw : ∀ kf ws u, W kf ws u → u.locals "jsc" = some A ∧ Dom A u.memaddrs := fun kf ws u hu =>
    ⟨by rw [hloc kf ws u hu]; exact hsp, by rw [(hmem kf ws u hu).1]; exact hdom⟩
  have hcount : ∀ kf ws u, W kf ws u → (∀ q ∈ ws, q.1 ≠ sCount) →
      eval u (.loadWord (.op .add (.var "jsc") (.const (BitVec.ofNat 64 sCount)))) =
        some (BitVec.ofNat 64 st.acc.length) := fun kf ws u hu hws =>
    eval_load (w := at_ A sCount) (by simp [eval, (hsw kf ws u hu).1, at_]) (by
      have := (hsw kf ws u hu).2 sCount (by decide)
      rwa [align_at h.hA, show sCount / 8 * 8 = sCount from rfl] at this)
      (by rw [hu.rest sCount (by decide) (by decide) hws (Or.inr (Or.inl (by decide)))]; exact hur.area.count)
  -- the test: a second format
  have hev0 : ∀ u, W false [] u → eval u (.op .and_ (.cmp .less (.const (BitVec.ofNat 64 0))
      (.loadWord (.op .add (.var "jsc") (.const (BitVec.ofNat 64 sCount)))))
      (.cmp .equal (.var "jrec") (.const (BitVec.ofNat 64 formatType)))) =
      some (bw (decide (0 < st.acc.length) && decide (rec.type = formatType))) := fun u hu =>
    eval_and (eval_lt (by decide) (by omega) rfl (hcount false [] u hu fun _ hq => (nomatch hq)))
      (eval_eq (by omega) (by decide) (by simp only [eval]; rw [hloc _ _ u hu]; exact hjrec) rfl)
  have hWc : ∀ kf ws, Safe.ClockFree (W kf ws) := fun _ _ => accAt_clock
  have hAc : Safe.ClockFree (AccOut A J st s0 rec taken) := fun c u ⟨h1, h2⟩ => ⟨{ h1 with }, outAt_clock _ c u h2⟩
  have hkept : ∀ kf ws u, W kf ws u → Kept ScanProg.locals (AreaW A) s0 u := fun _ _ u hu =>
    kept_trans hur.kept (kept_widen hu.kept (fun _ h => nomatch h) fun _ h => h)
  have store : ∀ kf ws (x : Nat) (e : Syntax.PExpr) (E : PancakeExp), Lower.lowerExp e = some E → x < sKey →
      x % 8 = 0 → x ≠ 0 → (∀ q ∈ ws, q.1 ≠ x) → ∀ (val : Word), (∀ u, W kf ws u → eval u E = some val) →
      Frag o [ScanProg.setw x e] (W kf ws) (W kf ((x, val) :: ws)) := fun kf ws x e E he hx hx8 hx0 hxw val hv =>
    setw_frag o h.hA hx8 (by simp only [ScanProg.size]; omega) hx0 he (hWc _ _) fun u hu =>
      ⟨(hsw kf ws u hu).1, (hsw kf ws u hu).2, val, hv u hu, accAt_store h.hA hu hx hx8 hxw val⟩
  refine frag_conseq (P0 := W false []) ?_ (fun u hu => ⟨kept_of_like hu, fun _ hq => (nomatch hq),
    fun _ hq => (nomatch hq), fun x _ _ _ _ => by rw [hu.memory], fun e => by cases e⟩) fun _ h => h
  refine frag_ite o (C := .op .and_ (.cmp .less (.const (BitVec.ofNat 64 0))
      (.loadWord (.op .add (.var "jsc") (.const (BitVec.ofNat 64 sCount)))))
      (.cmp .equal (.var "jrec") (.const (BitVec.ofNat 64 formatType)))) rfl hAc (fun u hu => ⟨_, hev0 u hu⟩)
    ?_ (noDecl _ rfl) ?_ (noDecl _ rfl)
  · -- a second format
    refine frag_pure (0 < st.acc.length ∧ rec.type = formatType) (fun u ⟨hu, hne⟩ => by
      rw [hev0 u hu] at hne; simpa using bw_ne0 hne) (lowK_any _ (k := .skip) (c := _) rfl) fun hc => ?_
    refine frag_conseq (frag_append (xs := [_])
      (store false [] sStatus _ (.const (BitVec.ofNat 64 corrupt)) rfl (by decide) (by decide) (by decide)
        (fun _ hq => (nomatch hq)) _ fun _ _ => rfl)
      (store false _ sWhy _ (.const (BitVec.ofNat 64 (whyCode .formatAgain))) rfl (by decide) (by decide) (by decide)
        (by simp [sStatus, sWhy]) _ fun _ _ => rfl)) (fun u hu => hu.1) fun u hu => ⟨hkept _ _ u hu, ?_⟩
    have hif : (!st.acc.isEmpty && rec.key.isSome) = true := by
      rw [record_key, decide_eq_true hc.2]
      cases e : st.acc with
      | nil => rw [e] at hc; simp at hc
      | cons _ _ => rfl
    rw [if_pos hif]
    have harea : AreaAt A J st u := areaAt_keep h.hA hur.area h.valid.len hu.kept.memaddrs hu.kept.be
      fun x hx hx8 hr => hu.rest x hx hx8 (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, sStatus, sWhy] at hr ⊢
        omega) (Or.inl rfl)
    exact ⟨hu.stored (sStatus, BitVec.ofNat 64 corrupt) (by simp), by
      rw [hu.rest sPos (by decide) (by decide) (by simp [sStatus, sWhy, sPos]) (Or.inl rfl)]; exact hur.area.pos,
      hu.stored (sWhy, BitVec.ofNat 64 (whyCode .formatAgain)) (by simp), harea⟩
  · -- the record taken
    refine frag_pure (¬ (0 < st.acc.length ∧ rec.type = formatType)) (fun u ⟨hu, h0⟩ => by
      rw [hev0 u hu] at h0; have := bw_eq0 h0; simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not] at this
      omega) (lowK_any _ (k := .skip) (c := _) rfl) fun hc => ?_
    refine frag_conseq (P0 := W false []) ?_ (fun u hu => hu.1) fun _ h => h
    have hif : (!st.acc.isEmpty && rec.key.isSome) = false := by
      rw [record_key]
      by_cases hfm : rec.type = formatType
      · have : st.acc = [] := List.eq_nil_of_length_eq_zero (by omega)
        simp [this]
      · simp [hfm]
    -- the count, the type, where the next frame starts, and the status
    let Wfin : List (Nat × Word) := [(sStatus, BitVec.ofNat 64 ScanProg.record),
      (sPos, BitVec.ofNat 64 (st.pos + taken)), (sType, BitVec.ofNat 64 rec.type),
      (sCount, BitVec.ofNat 64 (st.acc.length + 1))]
    have tail : ∀ kf (ws0 : List (Nat × Word)), (∀ q ∈ ws0, q.1 = sKeyed) →
        Frag o ScanProg.acceptTail (W kf ws0) (W kf (Wfin ++ ws0)) := by
      intro kf ws0 hws
      have hne : ∀ x, x ≠ sKeyed → ∀ q ∈ ws0, q.1 ≠ x := fun x hx q hq e => hx (e ▸ hws q hq)
      refine frag_append (xs := [_]) (store kf ws0 sCount _
        (.op .add (.loadWord (.op .add (.var "jsc") (.const (BitVec.ofNat 64 sCount)))) (.const (BitVec.ofNat 64 1)))
        rfl (by decide) (by decide) (by decide) (hne _ (by decide)) (BitVec.ofNat 64 (st.acc.length + 1))
        fun u hu => eval_addc 1 (hcount kf ws0 u hu (hne _ (by decide)))) ?_
      refine frag_append (xs := [_]) (store kf _ sType _ (.var "jrec") rfl (by decide) (by decide) (by decide)
        (by simp only [List.mem_cons, forall_eq_or_imp]; exact ⟨by decide, hne _ (by decide)⟩)
        (BitVec.ofNat 64 rec.type) fun u hu => by simp only [eval]; rw [hloc _ _ u hu]; exact hjrec) ?_
      refine frag_append (xs := [_]) (store kf _ sPos _
        (.op .add (.var "jp") (.op .add (.var "jpl") (.const (BitVec.ofNat 64 (headerLength + 1))))) rfl (by decide)
        (by decide) (by decide)
        (by simp only [List.mem_cons, forall_eq_or_imp]; exact ⟨by decide, by decide, hne _ (by decide)⟩)
        (BitVec.ofNat 64 (st.pos + taken)) fun u hu => ?_) ?_
      · rw [eval_add (by simp only [eval]; rw [hloc _ _ u hu]; exact hjp)
          (eval_addc _ (by simp only [eval]; rw [hloc _ _ u hu]; exact hjpl))]
        congr 2; simp only [headerLength]; omega
      · exact store kf _ sStatus _ (.const (BitVec.ofNat 64 ScanProg.record)) rfl (by decide) (by decide)
          (by decide) (by simp only [List.mem_cons, forall_eq_or_imp]; exact ⟨by decide, by decide, by decide,
            hne _ (by decide)⟩) _ fun _ _ => rfl
    -- the record's state in the area
    have final : ∀ kf (ws0 : List (Nat × Word)) u, (∀ q ∈ ws0, q.1 = sKeyed) → W kf (Wfin ++ ws0) u →
        u.memory (at_ A sKeyed) = bw (st.key <|> rec.key).isSome →
        (∀ k, (st.key <|> rec.key) = some k → readByteArray u.memory u.memaddrs u.be (at_ A sKey) 16 = some k) →
        AccOut A J st s0 rec taken u := fun kf ws0 u hws hu hkd hky => by
      refine ⟨hkept _ _ u hu, ?_⟩
      rw [if_neg (by rw [hif]; decide)]
      have hnot : ∀ x, x ≠ sStatus → x ≠ sPos → x ≠ sType → x ≠ sCount → x ≠ sKeyed → ∀ q ∈ Wfin ++ ws0, q.1 ≠ x :=
        fun x h3 h4 h5 h6 h7 q hq => by
          simp only [Wfin, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq
          rcases hq with (rfl | rfl | rfl | rfl) | hq
          · exact Ne.symm h3
          · exact Ne.symm h4
          · exact Ne.symm h5
          · exact Ne.symm h6
          · rw [hws q hq]; exact Ne.symm h7
      have hr : ∀ x, x < ScanProg.size → x % 8 = 0 → x ≠ sStatus → x ≠ sPos → x ≠ sType → x ≠ sCount →
          x ≠ sKeyed → (kf = false ∨ x < sKey ∨ sMessage ≤ x) → u.memory (at_ A x) = ur.memory (at_ A x) :=
        fun x hx hx8 h3 h4 h5 h6 h7 hk => hu.rest x hx hx8 (hnot x h3 h4 h5 h6 h7) hk
      have hst' := hu.stored
      refine ⟨hst' (sStatus, BitVec.ofNat 64 ScanProg.record) (by simp [Wfin]), ⟨?_, ?_, ?_,
        hst' (sPos, BitVec.ofNat 64 (st.pos + taken)) (by simp [Wfin]), hkd,
        hst' (sCount, BitVec.ofNat 64 (st.acc.length + 1)) (by simp [Wfin]), fun i hi => ?_, hky⟩,
        hst' (sType, BitVec.ofNat 64 rec.type) (by simp [Wfin]), fun c hc => ?_⟩
      · rw [hr sSize (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (Or.inr (Or.inl (by decide)))]; exact hur.area.size
      · rw [hr sBase (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (Or.inr (Or.inl (by decide)))]; exact hur.area.base
      · rw [hr sLen (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (Or.inr (Or.inl (by decide)))]; exact hur.area.len
      · have hi' : i < st.len := hi
        have := hur.area.window i hi'
        simp only [memLoadByte, align_at h.hA] at this ⊢
        rw [hu.kept.memaddrs, hu.kept.be, hr _ (by simp only [ScanProg.size]; omega) (by omega)
          (by simp only [sStatus]; omega) (by simp only [sPos]; omega) (by simp only [sType]; omega)
          (by simp only [sCount]; omega) (by simp only [sKeyed]; omega) (Or.inr (Or.inr (by omega)))]
        exact this
      · subst hc
        refine commitAt_of (hcom _ rfl) (decode_groups (recordOf_commit hro)) fun x h1 h2 h3 => ?_
        simp only [sSeq] at h1
        exact hr x (by simp only [ScanProg.size]; omega) h3 (by simp only [sStatus]; omega)
          (by simp only [sPos]; omega) (by simp only [sType]; omega) (by simp only [sCount]; omega)
          (by simp only [sKeyed]; omega) (Or.inr (Or.inl h2))
    by_cases hfm : rec.type = formatType
    · -- a format: its key copied, the key's flag set
      obtain ⟨k, rfl⟩ : ∃ k, rec = .format k := by
        cases rec with
        | format k => exact ⟨k, rfl⟩
        | commit _ => simp [Record.type, formatType, commitType] at hfm
        | start => simp [Record.type, formatType, startType] at hfm
      obtain ⟨hk36, hkk⟩ := recordOf_format hro
      have hacc : st.acc = [] := List.eq_nil_of_length_eq_zero (by omega)
      have hkey0 : st.key = none := by
        cases e : st.key with
        | none => rfl
        | some _ => exact absurd (hv.keyed (by simp [e])) (by simp [hacc])
      have hkb : kb.length = 16 := by simp only [kb, List.length_drop, hk36]
      have hevj : ∀ u, W false [] u → eval u (.cmp .equal (.var "jrec") (.const (BitVec.ofNat 64 formatType))) =
          some (bw true) := fun u hu => by
        rw [eval_eq (x := formatType) (y := formatType) (by decide) (by decide)
          (by simp only [eval]; rw [hloc _ _ u hu]; exact hjrec) rfl]
        simp
      let Fk : Assn σ := fun u => Kept [] (AreaW A) ur u ∧ ∀ x, x < ScanProg.size → x % 8 = 0 →
        (x < sKey ∨ sMessage ≤ x) → u.memory (at_ A x) = ur.memory (at_ A x)
      have hFkc : Safe.ClockFree Fk := fun _ _ ⟨h1, h2⟩ => ⟨{ h1 with }, h2⟩
      have hFk : ∀ u a b, Fk u → KeyW A (byteAlign a) → Fk { u with memory := putByte u.memory u.be a b } :=
        fun u a b hu ⟨y, hy1, hy2, e⟩ => ⟨kept_put hu.1 ⟨y, by simp only [ScanProg.size]; omega, e⟩ _ _,
          fun x hx hx8 hr => by
            simp only [putByte]
            rw [if_neg (fun e' => by rw [e] at e'; have := at_inj (A := A) (by omega) (by omega) e'; omega)]
            exact hu.2 x hx hx8 hr⟩
      have hkc := keyCopy_frag o h.hA (o' := st.pos - st.base) hkb hFkc hFk
        (fun u hu => by rw [hu.1.locals _ List.not_mem_nil]; exact hsp)
        (fun u hu => by rw [hu.1.locals _ List.not_mem_nil]; exact hjpp)
        (fun u hu => by rw [hu.1.memaddrs]; exact hdom)
        (fun u hu i hi => by
          have hwin := hur.area.window (st.pos - st.base + 13 + (20 + i)) (by omega)
          simp only [memLoadByte, align_at h.hA] at hwin ⊢
          rw [hu.1.memaddrs, hu.1.be, hu.2 _ (by simp only [ScanProg.size]; omega) (by omega) (Or.inr (by omega)),
            show sWindow + (st.pos - st.base) + 13 + (20 + i) = sWindow + (st.pos - st.base + 13 + (20 + i)) by omega]
          rw [hwin, show st.base + (st.pos - st.base + 13 + (20 + i)) = st.pos + (13 + (20 + i)) by omega]
          simp only [kb, List.getD_eq_getElem?_getD, List.getElem?_drop]
          rw [List.getElem?_eq_getElem (show 20 + i < (payloadOf (J.drop st.pos)).length by omega),
            payload_get _ _ (by simp only [List.length_drop]; omega), List.getElem_drop,
            List.getElem?_eq_getElem (by omega)])
      refine frag_append (xs := [_]) (frag_ite o (C := .cmp .equal (.var "jrec")
        (.const (BitVec.ofNat 64 formatType))) rfl (hWc true [(sKeyed, BitVec.ofNat 64 1)])
        (fun u hu => ⟨_, hevj u hu⟩) ?_ (noDecl _ rfl)
        (frag_nil o fun u ⟨hu, h0⟩ => absurd (h0 ▸ hevj u hu) (by simp [bw])) (noDecl _ rfl))
        (frag_conseq (tail true [(sKeyed, BitVec.ofNat 64 1)] (by simp)) (fun _ h => h) fun u hu =>
          final true _ u (by simp) hu ?_ ?_)
      · refine frag_append (frag_conseq hkc (fun u ⟨hu, _⟩ => ⟨hu.kept, fun x hx hx8 _ =>
          hu.rest x hx hx8 (fun _ hq => (nomatch hq)) (Or.inl rfl)⟩) fun u ⟨hu, hrd⟩ =>
          (⟨hu.1, fun _ hq => (nomatch hq), fun _ hq => (nomatch hq), fun x hx hx8 _ hk => by
            rcases hk with hk | hk
            · cases hk
            · exact hu.2 x hx hx8 hk, fun _ => hrd⟩ : W true [] u))
          (store true [] sKeyed _ (.const (BitVec.ofNat 64 1)) rfl (by decide) (by decide) (by decide)
            (fun _ hq => (nomatch hq)) _ fun _ _ => rfl)
      · rw [hkey0]
        simpa [Record.key, bw] using hu.stored (sKeyed, BitVec.ofNat 64 1) (by simp [Wfin])
      · intro k' hk'
        rw [hkey0] at hk'
        have e : k = k' := by simpa [Record.key] using hk'
        subst e
        rw [hkk]
        exact hu.key rfl
    · -- no format: the key as it was
      have hrk : rec.key = none := by
        have := record_key rec; rw [decide_eq_false hfm] at this; simpa using this
      have hevj : ∀ u, W false [] u → eval u (.cmp .equal (.var "jrec") (.const (BitVec.ofNat 64 formatType))) =
          some (bw false) := fun u hu => by
        rw [eval_eq (x := rec.type) (y := formatType) (by omega) (by decide)
          (by simp only [eval]; rw [hloc _ _ u hu]; exact hjrec) rfl]
        simp [hfm]
      refine frag_append (xs := [_]) (frag_ite o (C := .cmp .equal (.var "jrec")
        (.const (BitVec.ofNat 64 formatType))) rfl (hWc false []) (fun u hu => ⟨_, hevj u hu⟩)
        (frag_unsat (lowK_any _ (k := .skip) (c := _) rfl) fun u ⟨hu, hne⟩ => hne (by rw [hevj u hu]; rfl))
        (noDecl _ rfl) (frag_nil o fun u ⟨hu, _⟩ => hu) (noDecl _ rfl))
        (frag_conseq (tail false [] (fun _ hq => (nomatch hq))) (fun _ h => h) fun u hu =>
          final false [] u (fun _ hq => (nomatch hq)) hu ?_ ?_)
      · have e : (st.key <|> rec.key) = st.key := by rw [hrk]; cases st.key <;> rfl
        rw [e, hu.rest sKeyed (by decide) (by decide) (by simp [Wfin, sStatus, sPos, sType, sCount, sKeyed])
          (Or.inl rfl)]
        exact hur.area.keyed
      · intro k hk
        have e : (st.key <|> rec.key) = st.key := by rw [hrk]; cases st.key <;> rfl
        rw [e] at hk
        rw [← hur.area.key k hk, hu.kept.memaddrs, hu.kept.be]
        refine readByteArray_congr 16 _ fun j hj => ?_
        simp only [memLoadByte, at_add, align_at h.hA]
        rw [hu.rest _ (by simp only [ScanProg.size]; omega) (by omega)
          (by simp [Wfin, sStatus, sPos, sType, sCount]; omega) (Or.inl rfl)]

end DN.News.ScanRun
