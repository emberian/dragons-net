-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.ScanRead

/-!
# DN.News.ScanStop

If it goes on, where reading stops the step says torn tail when a torn append can leave the frame, what is
left fits that append and no frame that checks under the key starts after its first octet, and corruption
otherwise, as `Journal.stop` does (`stopped_frag`); and the scanner's whole step is `stepSpec`
(`step_frag`), from the kernel's entry too (`kernel_frag`). After a want, the window the host fills holds the
state with the octets added (`areaAt_fill`).
-/

namespace DN.News.ScanRun

open DN.Compiler DN.Compiler.Frag DN.Compiler.Bytes DN.News.Journal DN.News.ScanProg
open DN.News.FramerCode (bw bw_ne0 bw_eq0 eval_lt eval_le eval_eq eval_and)
open DN.Compiler.WpBytes (eval_addc eval_add)

variable {σ : Type}

/-! ## A stop: torn tail or corruption -/

/-- What `stopped` leaves where reading stops: the status, torn or corrupt, and why. -/
def StopOut (A : Word) (J : Bytes) (st : St) (s0 : PancakeState σ) (why : Why) (u : PancakeState σ) : Prop :=
  Kept ScanProg.locals (AreaW A) s0 u ∧ OutAt A J st (.stop (stop spec st.pos (J.drop st.pos) st.key why)) u

/-- The step's parts lower, given `fail` does. -/
theorem lowKK_frameAt {fail : List Syntax.PStmt} (hfl : LowKK fail) : LowKK (ScanProg.frameAt fail) :=
  lowKK_append (xs := [_]) (lowK_any _ (k := .skip) (c := _) rfl) (lowKK_append (xs := [_])
    (lowKK_ite rfl hfl (fun k => ⟨k, rfl⟩)) (lowK_any _ (k := .skip) (c := _) rfl))

/-- The search after a torn frame's first octet for one that checks. -/
theorem lowKK_tornLoop {fail : List Syntax.PStmt} (hfl : LowKK fail) : LowKK (ScanProg.tornLoop fail) :=
  lowKK_append (lowKK_append (lowKK_append (lowKK_frameAt hfl) (lowK_any _ (k := .skip) (c := _) rfl))
    (lowKK_frameWhy true)) (lowK_any _ (k := .skip) (c := _) rfl)

theorem lowKK_tornSearch {fail : List Syntax.PStmt} (hfl : LowKK fail) : LowKK (ScanProg.tornSearch fail) :=
  lowKK_append (xs := [_]) (lowK_any _ (k := .skip) (c := _) rfl) (lowKK_while rfl (lowKK_tornLoop hfl))

theorem lowKK_tornPart {fail : List Syntax.PStmt} (hfl : LowKK fail) : LowKK (ScanProg.tornPart fail) :=
  lowKK_append (xs := [_]) (lowK_any _ (k := .skip) (c := _) rfl) (lowKK_append (xs := [_])
    (lowK_any _ (k := .skip) (c := _) rfl) (lowKK_ite rfl (lowKK_append (xs := [_])
      (lowK_any _ (k := .skip) (c := _) rfl) (lowKK_ite rfl (lowKK_tornSearch hfl)
        (lowK_any _ (k := .skip) (c := _) rfl))) (lowK_any _ (k := .skip) (c := _) rfl)))

/-- The names the search sets. -/
def tornNames : List String := ["jq", "jtorn", "jo", "jf", "jpp", "jr"] ++ fwNames

/-- The search's state after `i` places from the one after `jp`: where it is, and whether no frame that checks
under `k` started at one, the rest as `l` lists it. -/
def TornAt (A : Word) (J : Bytes) (st : St) (s0 : PancakeState σ) (k : Bytes) (l : List (String × Value)) (i : Nat)
    (u : PancakeState σ) : Prop :=
  Ctx A J st s0 (("jq", BitVec.ofNat 64 (st.pos + 1 + i)) :: ("jtorn", bw (!seen J k (st.pos + 1) i)) :: l) u ∧
    i ≤ J.length - (st.pos + 1)

theorem tornAt_clock {A : Word} {J : Bytes} {st : St} {s0 : PancakeState σ} {k : Bytes} {l : List (String × Value)}
    (i : Nat) : Safe.ClockFree (TornAt A J st s0 k l i) := fun _ _ ⟨h1, h2⟩ => ⟨ctx_clock _ _ h1, h2⟩

/-- **One place searched**: if it goes on, the frame there is checked under the journal's key `k`, and one that
checks ends the search. -/
theorem tornStep_frag (o : Oracle σ) {A : Word} {J : Bytes} {st : St} {s0 : PancakeState σ} (h : StepIn A J st s0)
    {fail : List Syntax.PStmt} (hfl : LowKK fail) (hfd : declared fail = []) {k : Bytes} (hk : st.key = some k)
    {l : List (String × Value)} (hwin : J.length ≤ st.base + st.len)
    (hjsz : l.lookup "jsz" = some (BitVec.ofNat 64 J.length)) (hjb : l.lookup "jb" = some (BitVec.ofNat 64 st.base))
    (hjw : l.lookup "jw" = some (at_ A sWindow)) (hout : Outside tornNames l = true) (i : Nat)
    (hg : (!seen J k (st.pos + 1) i && decide (st.pos + 1 + i < J.length)) = true) :
    Frag o (ScanProg.tornLoop fail) (TornAt A J st s0 k l i) (TornAt A J st s0 k l (i + 1)) := by
  have hn := nums
  have hJ := h.short
  have hbp := h.valid.base
  have hlen := h.valid.len
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_true_eq] at hg
  obtain ⟨hsi, hqi⟩ := hg
  obtain ⟨q, hq⟩ : ∃ q, q = st.pos + 1 + i := ⟨_, rfl⟩
  have hqJ : q < J.length := by omega
  have hf : ∀ y ∈ tornNames, Fresh y l = true := fun y hy => fresh_of_outside hout hy
  have hfw : Outside fwNames l = true := by
    simp only [Outside, List.all_eq_true] at hout ⊢
    intro p hp
    have := hout p hp
    simp only [tornNames, List.contains_append, Bool.not_or, Bool.and_eq_true] at this
    exact this.2
  let L0 : List (String × Value) := ("jq", BitVec.ofNat 64 q) :: ("jtorn", bw true) :: l
  refine frag_conseq (P0 := Ctx A J st s0 L0) ?_ (fun u ⟨hu, _⟩ => by
    have hv := hu.vals; rw [hsi, ← hq] at hv; exact ⟨hu.kept, hu.area, hv⟩) fun _ h => h
  -- the frame's place, what is left of the journal, and the frame checked under the key
  have f1 := frameAt_frag o h hfl hfd (q := q) (l := L0) (by omega) (by omega) (by omega) rfl hjb hjw
    (hf "jo" (by decide)) (hf "jf" (by decide)) (hf "jpp" (by decide))
  let L1 : List (String × Value) := ("jpp", at_ A (sWindow + (q - st.base) + 13)) ::
    ("jf", at_ A (sWindow + (q - st.base))) :: ("jo", BitVec.ofNat 64 (q - st.base)) :: L0
  have f2 := ctx_assign o h (x := "jr") (e := Syntax.eSub (Syntax.v "jsz") (Syntax.v "jq"))
    (E := .op .sub (.var "jsz") (.var "jq")) rfl (by decide) (l := L1) (hf "jr" (by decide))
    (v := BitVec.ofNat 64 (J.length - q)) fun u hu => by
      simp only [eval, vals_lookup hu.vals (x := "jsz") (l := L1) hjsz, vals_lookup hu.vals (x := "jq") (l := L1) rfl]
      rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)]
  let L2 : List (String × Value) := ("jr", BitVec.ofNat 64 (J.length - q)) :: L1
  have f3 := frameCheck_frag o h true (q := q) (l := L2) (by omega) hqJ (by omega) rfl rfl rfl (fun e => by cases e)
    (fun _ => by rw [hk]; rfl) hfw
  -- one that checks ends the search
  have hseen : seen J k (st.pos + 1) (i + 1) = (fault st.key q (J.drop q)).isNone := by
    rw [seen_succ, hsi, Bool.false_or, ← hq, checks_fault, hk]
  let pre : List (String × Value) := [("jr", BitVec.ofNat 64 (J.length - q)),
    ("jpp", at_ A (sWindow + (q - st.base) + 13)), ("jf", at_ A (sWindow + (q - st.base))),
    ("jo", BitVec.ofNat 64 (q - st.base)), ("jq", BitVec.ofNat 64 q)]
  let P4 (u : PancakeState σ) : Prop := Ctx A J st s0 L2 u ∧
    u.locals "jwhy" = some (BitVec.ofNat 64 (codeOf (fault st.key q (J.drop q))))
  have hev : ∀ u, P4 u → eval u (.cmp .equal (.var "jwhy") (.const 0)) =
      some (bw (decide (codeOf (fault st.key q (J.drop q)) = 0))) := fun u hu =>
    eval_eq (y := 0) codeOf_lt (by decide) (by simp only [eval]; exact hu.2) rfl
  have f4 : Frag o [ScanProg.tornNext] P4
      (Ctx A J st s0 (pre ++ ("jtorn", bw (!seen J k (st.pos + 1) (i + 1))) :: l)) := by
    refine frag_ite o (C := .cmp .equal (.var "jwhy") (.const 0)) rfl ctx_clock (fun u hu => ⟨_, hev u hu⟩) ?_
      (noDecl _ rfl) (frag_nil o fun u ⟨hu, h0⟩ => ?_) (noDecl _ rfl)
    · refine frag_pure (fault st.key q (J.drop q) = none) (fun u ⟨hu, hne⟩ => by
        rw [hev u hu] at hne; exact codeOf_zero.mp (by simpa using bw_ne0 hne))
        (lowK_any _ (k := .skip) (c := _) rfl) fun hfn => ?_
      have hv : bw (!seen J k (st.pos + 1) (i + 1)) = 0 := by rw [hseen, hfn]; rfl
      rw [hv]
      exact frag_conseq (ctx_reassign o h (x := "jtorn") (e := lit 0) (E := .op .add (.var "jz") (.const 0)) rfl
        (by decide) (pre := pre) (l := l) (w := bw true) rfl (hf "jtorn" (by decide)) (v := 0)
        fun u hu => by simp [eval, ctx_jz h hu]) (fun u hu => hu.1.1) fun _ h => h
    · rw [hev u hu] at h0
      have hf0 := bw_eq0 h0
      simp only [decide_eq_false_iff_not] at hf0
      have hs : seen J k (st.pos + 1) (i + 1) = false := by
        rw [hseen]
        cases e : fault st.key q (J.drop q) with
        | none => exact absurd (codeOf_zero.mpr e) hf0
        | some _ => rfl
      rw [hs]
      exact hu.1
  -- and the next place
  have f5 := ctx_reassign o h (x := "jq") (e := Syntax.eAdd (Syntax.v "jq") (Syntax.n 1))
    (E := .op .add (.var "jq") (.const 1)) rfl (by decide) (pre := pre.take 4)
    (l := ("jtorn", bw (!seen J k (st.pos + 1) (i + 1))) :: l) (w := BitVec.ofNat 64 q) rfl
    (hf "jq" (by decide)) (v := BitVec.ofNat 64 (q + 1)) fun u hu => eval_addc 1 (by
      simp only [eval]; exact vals_lookup hu.vals rfl)
  refine frag_conseq (frag_append (frag_append (frag_append f1 f2) f3)
    (frag_append (xs := [_]) (frag_conseq f4 (fun u hu => ⟨hu.1, hu.2.1⟩) fun _ h => h) f5)) (fun _ h => h)
    fun u hu => ⟨⟨hu.kept, hu.area, ?_⟩, by omega⟩
  have hv := vals_drop (pre := pre.take 4) hu.vals
  rw [show q + 1 = st.pos + 1 + (i + 1) by omega] at hv
  exact hv

/-- **The search after a torn frame's first octet**: if it goes on, `jtorn` says whether no frame that checks under
the journal's key `k` starts there or after, as `anyChecks` does. -/
theorem tornSearch_frag (o : Oracle σ) {A : Word} {J : Bytes} {st : St} {s0 : PancakeState σ} (h : StepIn A J st s0)
    {fail : List Syntax.PStmt} (hfl : LowKK fail) (hfd : declared fail = []) {k : Bytes} (hk : st.key = some k)
    {l : List (String × Value)} (hwin : J.length ≤ st.base + st.len)
    (hjsz : l.lookup "jsz" = some (BitVec.ofNat 64 J.length)) (hjb : l.lookup "jb" = some (BitVec.ofNat 64 st.base))
    (hjp : l.lookup "jp" = some (BitVec.ofNat 64 st.pos)) (hjw : l.lookup "jw" = some (at_ A sWindow))
    (hout : Outside tornNames l = true) :
    Frag o (ScanProg.tornSearch fail) (Ctx A J st s0 (("jtorn", bw true) :: l))
      (Ctx A J st s0 (("jtorn", bw (!anyChecks spec k (st.pos + 1) (J.drop (st.pos + 1)))) :: l)) := by
  have hn := nums
  have hJ := h.short
  have hpl := h.valid.pos
  have hst := h.valid.stop
  obtain ⟨n, hnd⟩ : ∃ n, n = J.length - (st.pos + 1) := ⟨_, rfl⟩
  have l0 := ctx_assign o h (x := "jq") (e := Syntax.eAdd (Syntax.v "jp") (Syntax.n 1))
    (E := .op .add (.var "jp") (.const 1)) rfl (by decide) (l := ("jtorn", bw true) :: l)
    (fresh_of_outside hout (by decide)) (v := BitVec.ofNat 64 (st.pos + 1 + 0)) fun u hu => eval_addc 1 (by
      simp only [eval]; exact vals_lookup hu.vals hjp)
  have hl := frag_count o (c := ScanProg.tornGo)
    (C := .op .and_ (.var "jtorn") (.cmp .less (.var "jq") (.var "jsz"))) rfl (lowKK_tornLoop hfl)
    (I := TornAt A J st s0 k l) tornAt_clock
    (fun _ _ _ _ _ hy => by rw [show declared (ScanProg.tornLoop fail) = [] from rfl] at hy; cases hy)
    (g := fun i => !seen J k (st.pos + 1) i && decide (st.pos + 1 + i < J.length))
    (fun i u hu => by
      have := hu.2
      rw [eval_and (p := !seen J k (st.pos + 1) i) (q := decide (st.pos + 1 + i < J.length))
        (by simp only [eval]; exact vals_lookup hu.1.vals rfl)
        (eval_lt (x := st.pos + 1 + i) (y := J.length) (by omega) (by omega)
          (by simp only [eval]; exact vals_lookup hu.1.vals rfl)
          (by simp only [eval]; exact vals_lookup hu.1.vals (x := "jsz") hjsz))]
      rfl)
    (fun i hg => tornStep_frag o h hfl hfd hk hwin hjsz hjb hjw hout i hg) 0
  refine frag_append (xs := [_]) (frag_conseq l0 (fun _ h => h) fun u hu => ⟨hu, Nat.zero_le _⟩)
    (frag_conseq hl (fun _ h => h) fun u ⟨i, hu, hg⟩ => ?_)
  have hi := hu.2
  have hjt : bw (!anyChecks spec k (st.pos + 1) (J.drop (st.pos + 1))) = bw (!seen J k (st.pos + 1) i) := by
    rw [anyChecks_seen J k n (st.pos + 1) (by omega)]
    cases hs : seen J k (st.pos + 1) i
    · simp only [hs, Bool.not_false, Bool.true_and, decide_eq_false_iff_not, Nat.not_lt] at hg
      have : i = n := by omega
      subst this; rw [hs]
    · rw [seen_mono J k _ (by omega : i ≤ n) hs]
  rw [hjt]
  exact ⟨hu.1.kept, hu.1.area, vals_drop (pre := [("jq", BitVec.ofNat 64 (st.pos + 1 + i))]) hu.1.vals⟩

/-- The step's state, kept where a word from the status's to the key's is stored. -/
theorem ctx_word {A : Word} {J : Bytes} {st : St} {s0 : PancakeState σ} (h : StepIn A J st s0)
    {l : List (String × Value)} {u : PancakeState σ} (hu : Ctx A J st s0 l u) {x : Nat} (hx1 : sStatus ≤ x)
    (hx2 : x < sKey) (v : Word) : Ctx A J st s0 l { u with memory := fun k => if k = at_ A x then v else u.memory k } :=
  ⟨kept_word hu.kept ⟨x, by have := nums; omega, rfl⟩ v, areaAt_word h.hA hu.area h.valid.len hx1 hx2 v, hu.vals⟩

/-- **Where reading stops**: if it goes on, the status says torn tail or corruption as `Journal.stop` does, and
why. -/
theorem stopped_frag (o : Oracle σ) {A : Word} {J : Bytes} {st : St} {s0 : PancakeState σ} (h : StepIn A J st s0)
    {fail : List Syntax.PStmt} (hfl : LowKK fail) (hfd : declared fail = []) (hpos : st.pos < J.length)
    (hw : ¬ st.base + st.len < st.pos + min (J.length - st.pos) maxFrame) {why : Why}
    (hnx : next spec st.key st.pos (J.drop st.pos) = .bad why) :
    Frag o (ScanProg.stopped fail) (RcDone A J st s0) (StopOut A J st s0 why) := by
  have hn := nums
  have hJ := h.short
  have hlen := h.valid.len
  have hwc : whyCode why < 7 := by cases why <;> decide
  let wc := BitVec.ofNat 64 (whyCode why)
  let R : List (String × Value) := ("jmw", wc) :: (fixedV A J st).take 6
  have s1 : Frag o [.assign "jmw" (Syntax.v "jwhy")] (RcDone A J st s0) (Ctx A J st s0 R) :=
    set_frag o (E := .var "jwhy") rfl ctx_clock fun u hu => ⟨wc, by
        simp only [eval]; have := hu.why; rw [hnx] at this; exact this,
      kept_has hu.kept (h.bound "jmw" (by decide)),
      ⟨kept_set hu.kept (by decide) _, { hu.area with },
        vals_cons (vals_sub hu.vals fun q hq => List.mem_of_mem_take hq) rfl wc⟩⟩
  have s2 := ctx_assign o h (x := "jtorn") (e := lit 0) (E := .op .add (.var "jz") (.const 0)) rfl (by decide) (l := R)
    rfl (v := bw false) fun u hu => by simp [eval, ctx_jz h hu, bw]
  -- whether a torn append can leave the frame
  obtain ⟨bs, hbs⟩ : ∃ bs, bs = J.drop st.pos := ⟨_, rfl⟩
  have hbsl : bs.length = J.length - st.pos := by rw [hbs, List.length_drop]
  obtain ⟨X, hXd⟩ : ∃ X, X = if st.key.isSome then maxFrame else firstFrame := ⟨_, rfl⟩
  have hX : X ≤ maxFrame := by rw [hXd]; split <;> decide
  obtain ⟨tb, htbd⟩ : ∃ tb, tb = tornHere spec st.pos bs st.key why := ⟨_, rfl⟩
  have htorn : tb = (why.torn && decide (bs.length ≤ X) && !(st.key.any fun k => anyChecks spec k (st.pos + 1)
      bs.tail)) := by rw [htbd, hXd]; simp [tornHere]
  have hfit : bs.length ≤ X → J.length ≤ st.base + st.len := fun e => by
    have := Nat.min_eq_left (Nat.le_trans (hbsl ▸ e) hX)
    omega
  have hwin : tb = true → J.length ≤ st.base + st.len := fun e => by
    rw [htorn] at e
    simp only [Bool.and_eq_true, decide_eq_true_eq] at e
    exact hfit e.1.2
  let L0 : List (String × Value) := ("jtorn", bw false) :: R
  have s3 : Frag o [.ite (Syntax.eLt (Syntax.v "jmw") (Syntax.n (whyCode .notARecord))) (ScanProg.tornPart fail) []]
      (Ctx A J st s0 L0) (Ctx A J st s0 (("jtorn", bw tb) :: R)) := by
    have hev5 : ∀ u, Ctx A J st s0 L0 u → eval u (.cmp .less (.var "jmw")
        (.const (BitVec.ofNat 64 (whyCode .notARecord)))) = some (bw (decide (whyCode why < 5))) := fun u hu =>
      eval_lt (by omega) (by decide) (by simp only [eval]; exact vals_lookup hu.vals (x := "jmw") rfl) rfl
    refine frag_ite o (C := .cmp .less (.var "jmw") (.const (BitVec.ofNat 64 (whyCode .notARecord)))) rfl ctx_clock
      (fun u hu => ⟨_, hev5 u hu⟩) ?_ (noDecl _ rfl) (frag_nil o fun u ⟨hu, h0⟩ => ?_) (noDecl _ rfl)
    · refine frag_pure (why.torn = true) (fun u ⟨hu, hne⟩ => by
        rw [hev5 u hu] at hne; rw [← torn_code]; exact bw_ne0 hne) (lowKK_tornPart hfl) fun hwt => ?_
      have t1 := ctx_assign o h (x := "jx") (e := lit firstFrame)
        (E := .op .add (.var "jz") (.const (BitVec.ofNat 64 firstFrame))) rfl (by decide) (l := L0) rfl
        (v := BitVec.ofNat 64 firstFrame) fun u hu => by simp [eval, ctx_jz h hu]
      have t2 : Frag o [.ite (Syntax.v "jky") [.assign "jx" (lit maxFrame)] []]
          (Ctx A J st s0 (("jx", BitVec.ofNat 64 firstFrame) :: L0))
          (Ctx A J st s0 (("jx", BitVec.ofNat 64 X) :: L0)) :=
        flagIf_frag o (lowK_any _ (k := .skip) (c := _) rfl) rfl ctx_clock (b := st.key.isSome)
          (fun u hu => vals_lookup hu.vals (x := "jky") rfl)
          (fun hk => by
            rw [hXd, if_pos hk]
            exact ctx_reassign o h (x := "jx") (e := lit maxFrame)
              (E := .op .add (.var "jz") (.const (BitVec.ofNat 64 maxFrame))) rfl (by decide) (pre := []) (l := L0)
              rfl rfl fun u hu => by simp [eval, ctx_jz h hu])
          (fun hk u hu => by rw [hXd, if_neg (by simp [hk])]; exact hu)
      have hev6 : ∀ u, Ctx A J st s0 (("jx", BitVec.ofNat 64 X) :: L0) u →
          eval u (.cmp .notLess (.var "jx") (.var "jrem")) = some (bw (decide (bs.length ≤ X))) := fun u hu => by
        rw [hbsl]
        exact eval_le (by omega) (by omega) (by simp only [eval]; exact vals_lookup hu.vals (x := "jrem") rfl)
          (by simp only [eval]; exact vals_lookup hu.vals (x := "jx") rfl)
      have t3 : Frag o [ScanProg.tornCheck fail] (Ctx A J st s0 (("jx", BitVec.ofNat 64 X) :: L0))
          (Ctx A J st s0 (("jtorn", bw tb) :: R)) := by
        refine frag_ite o (C := .cmp .notLess (.var "jx") (.var "jrem")) rfl ctx_clock (fun u hu => ⟨_, hev6 u hu⟩)
          ?_ (noDecl _ rfl) (frag_nil o fun u ⟨hu, h0⟩ => ?_) (noDecl _ rfl)
        · refine frag_pure (bs.length ≤ X) (fun u ⟨hu, hne⟩ => by rw [hev6 u hu] at hne; simpa using bw_ne0 hne)
            (lowKK_append (xs := [_]) (lowK_any _ (k := .skip) (c := _) rfl) (lowKK_ite rfl (lowKK_tornSearch hfl)
              (lowK_any _ (k := .skip) (c := _) rfl))) fun hlX => ?_
          have t4 := ctx_reassign o h (x := "jtorn") (e := lit 1) (E := .op .add (.var "jz") (.const 1)) rfl
            (by decide) (pre := [("jx", BitVec.ofNat 64 X)]) (l := R) (w := bw false) rfl rfl (v := bw true)
            fun u hu => by simp [eval, ctx_jz h hu, bw]
          refine frag_append (xs := [_]) (frag_conseq t4 (fun u hu => hu.1) fun u hu =>
            (⟨hu.kept, hu.area, vals_drop (pre := [("jx", BitVec.ofNat 64 X)]) hu.vals⟩ :
              Ctx A J st s0 (("jtorn", bw true) :: R) u))
            (flagIf_frag o (lowKK_tornSearch hfl) rfl ctx_clock (fun u hu => vals_lookup hu.vals (x := "jky") rfl)
              (fun hk => ?_) (fun hk u hu => ?_))
          · obtain ⟨k, hk'⟩ : ∃ k, st.key = some k := Option.isSome_iff_exists.mp hk
            have htbn : tb = !anyChecks spec k (st.pos + 1) (J.drop (st.pos + 1)) := by
              rw [htorn, hwt, decide_eq_true hlX, hk', hbs, List.tail_drop]
              simp only [Option.any, Bool.true_and]
            rw [htbn]
            exact tornSearch_frag o h hfl hfd hk' (hfit hlX) rfl rfl rfl rfl rfl
          · have : tb = true := by
              rw [htorn, hwt, decide_eq_true hlX]
              cases e : st.key with
              | none => rfl
              | some _ => rw [e] at hk; cases hk
            rw [this]; exact hu
        · rw [hev6 u hu] at h0
          have hl := bw_eq0 h0
          have : tb = false := by rw [htorn, hl]; simp
          rw [this]
          exact ⟨hu.kept, hu.area, vals_drop (pre := [("jx", BitVec.ofNat 64 X)]) hu.vals⟩
      exact frag_conseq (frag_append (xs := [_]) t1 (frag_append (xs := [_]) t2 t3)) (fun u h => h.1) fun _ h => h
    · rw [hev5 u hu] at h0
      have h5 := bw_eq0 h0
      rw [torn_code] at h5
      have : tb = false := by rw [htorn, h5]; rfl
      rw [this]; exact hu
  -- the status, and why
  have hSc : Safe.ClockFree (StopOut A J st s0 why) := fun c u ⟨h1, h2⟩ => ⟨{ h1 with }, outAt_clock _ c u h2⟩
  have hjt : ∀ u, Ctx A J st s0 (("jtorn", bw tb) :: R) u → eval u (.var "jtorn") = some (bw tb) := fun u hu => by
    simp only [eval]; exact vals_lookup hu.vals rfl
  have s4 : Frag o [ScanProg.stopStatus] (Ctx A J st s0 (("jtorn", bw tb) :: R)) (StopOut A J st s0 why) := by
    refine frag_ite o (C := .var "jtorn") rfl hSc (fun u hu => ⟨_, hjt u hu⟩) ?_ (noDecl _ rfl) ?_ (noDecl _ rfl)
    · refine setw_frag o h.hA (by decide) (by decide) (E := .const (BitVec.ofNat 64 torn)) rfl hSc
        fun u ⟨hu, hne⟩ => ⟨ctx_jsc h hu, ctx_dom h hu, _, rfl, ?_⟩
      rw [hjt u hu] at hne
      have htb := bw_ne0 hne
      have htb' : tornHere spec st.pos (J.drop st.pos) st.key why = true := by rw [← hbs, ← htbd]; exact htb
      have hu' := ctx_word h hu (x := sStatus) (Nat.le_refl _) (by decide) (BitVec.ofNat 64 torn)
      refine ⟨hu'.kept, ?_⟩
      simp only [stop, htb', if_true, OutAt]
      exact ⟨by simp, hu'.area.pos, hu'.area, hwin htb⟩
    · refine frag_pure (tb = false) (fun u ⟨hu, h0⟩ => by rw [hjt u hu] at h0; exact bw_eq0 h0)
        (lowK_any _ (k := .skip) (c := _) rfl) fun htb => ?_
      let Q1 (u : PancakeState σ) : Prop := Ctx A J st s0 (("jtorn", bw tb) :: R) u ∧
        u.memory (at_ A sStatus) = BitVec.ofNat 64 corrupt
      have hQ1c : Safe.ClockFree Q1 := fun _ _ ⟨h1, h2⟩ => ⟨ctx_clock _ _ h1, h2⟩
      refine frag_append (xs := [_]) (setw_frag o h.hA (by decide) (by decide)
        (E := .const (BitVec.ofNat 64 corrupt)) rfl hQ1c fun u ⟨hu, _⟩ => ⟨ctx_jsc h hu, ctx_dom h hu, _, rfl,
          ctx_word h hu (x := sStatus) (Nat.le_refl _) (by decide) _, by simp⟩)
        (setw_frag o h.hA (by decide) (by decide) (E := .var "jmw") rfl hSc fun u hu =>
          ⟨ctx_jsc h hu.1, ctx_dom h hu.1, wc, by simp only [eval]; exact vals_lookup hu.1.vals (x := "jmw") rfl, ?_⟩)
      have htb' : tornHere spec st.pos (J.drop st.pos) st.key why = false := by rw [← hbs, ← htbd]; exact htb
      have hu' := ctx_word h hu.1 (by decide) (by decide) (x := sWhy) wc
      refine ⟨hu'.kept, ?_⟩
      simp only [stop, htb', OutAt]
      have e1 : at_ A sStatus ≠ at_ A sWhy := at_ne (by decide) (by decide) (by decide)
      exact ⟨by simp only [if_neg e1]; exact hu.2, hu'.area.pos, by simp [wc], hu'.area⟩
  exact frag_append (xs := [_]) s1 (frag_append (xs := [_]) s2 (frag_append (xs := [_]) s3 s4))

/-! ## The step -/

theorem lowKK_want {fail : List Syntax.PStmt} (hfl : LowKK fail) : LowKK (ScanProg.want fail) :=
  lowKK_append (xs := [_]) (lowK_any _ (k := .skip) (c := _) rfl) (lowKK_append (xs := [_])
    (lowKK_ite rfl hfl (fun k => ⟨k, rfl⟩)) (lowK_any _ (k := .skip) (c := _) rfl))

theorem lowKK_stopped {fail : List Syntax.PStmt} (hfl : LowKK fail) : LowKK (ScanProg.stopped fail) :=
  lowKK_append (xs := [_, _]) (lowK_any _ (k := .skip) (c := _) rfl) (lowKK_append (xs := [_])
    (lowKK_ite rfl (lowKK_tornPart hfl) (lowK_any _ (k := .skip) (c := _) rfl)) (lowK_any _ (k := .skip) (c := _) rfl))

theorem lowKK_frameRead {fail : List Syntax.PStmt} (hfl : LowKK fail) : LowKK (ScanProg.frameRead fail) :=
  lowKK_append (lowKK_append (lowKK_append (lowK_any _ (k := .skip) (c := _) rfl) (lowKK_frameAt hfl))
    (lowK_any _ (k := .skip) (c := _) rfl)) (lowKK_frameWhy false)

theorem lowKK_read {fail : List Syntax.PStmt} (hfl : LowKK fail) : LowKK (ScanProg.readPart fail) :=
  lowKK_append (lowKK_frameRead hfl) (lowKK_append (xs := [_])
    (lowKK_ite rfl (lowKK_recordOf hfl) (lowK_any _ (k := .skip) (c := _) rfl))
    (lowKK_ite rfl (lowKK_stopped hfl) lowKK_accept))

/-- **The scanner's step is `stepSpec`**: if it goes on, from the area holding a state of reading `J` that keeps
its window, the step leaves the status `stepSpec` gives, and with it the area's next state and the octets
wanted, the record read and its fields, or where and why reading stops. -/
theorem step_frag (o : Oracle σ) {A : Word} {J : Bytes} {st : St} {s0 : PancakeState σ} (h : StepIn A J st s0)
    {fail : List Syntax.PStmt} (hfl : LowKK fail) (hfd : declared fail = []) :
    Frag o (ScanProg.stepWith fail) (Like s0) (StepOut A J st s0) := by
  have hn := nums
  have hv := h.valid
  have hJ := h.short
  have hpl := hv.pos
  have hst := hv.stop
  have hSc : Safe.ClockFree (StepOut A J st s0) := stepOut_clock
  refine frag_append (head_frag o h hfl hfd) ?_
  have hev0 : ∀ u, Hd A J st s0 u → eval u (.cmp .equal (.var "jrem") (.const 0)) =
      some (bw (decide (J.length - st.pos = 0))) := fun u hu =>
    eval_eq (y := 0) (by omega) (by decide) (by simp only [eval]; exact hu.jrem) rfl
  refine frag_ite o (C := .cmp .equal (.var "jrem") (.const 0)) rfl hSc (fun u hu => ⟨_, hev0 u hu⟩) ?_
    (noDecl _ rfl) ?_ (noDecl _ rfl)
  · -- the journal's end
    refine setw_frag o h.hA (by decide) (by decide) (E := .const (BitVec.ofNat 64 clean)) rfl hSc
      fun u ⟨hu, hne⟩ => ⟨kept_jsc h hu.kept, kept_dom h hu.kept, _, rfl, ?_⟩
    rw [hev0 u hu] at hne
    have h0 : J.length ≤ st.pos := by have := bw_ne0 hne; simp at this; omega
    have hc := ctx_word h (hd_ctx h hu) (x := sStatus) (Nat.le_refl _) (by decide) (BitVec.ofNat 64 clean)
    refine ⟨hc.kept, ?_⟩
    simp only [stepSpec, if_pos h0, OutAt]
    exact ⟨by simp, hc.area⟩
  · refine frag_pure (st.pos < J.length) (fun u ⟨hu, h0⟩ => by
      rw [hev0 u hu] at h0; have := bw_eq0 h0; simp at this; omega)
      (lowKK_append (xs := [_]) (lowK_any _ (k := .skip) (c := _) rfl) (lowKK_append (xs := [_])
        (lowK_any _ (k := .skip) (c := _) rfl) (lowKK_ite rfl (lowKK_want hfl) (lowKK_read hfl)))) fun hpos => ?_
    have hHc : Safe.ClockFree (Hd A J st s0) := fun _ _ hu => { hu with kept := { hu.kept with } }
    let N1 (m : Nat) (u : PancakeState σ) : Prop := Hd A J st s0 u ∧ u.locals "jneed" = some (BitVec.ofNat 64 m)
    have hN1c : ∀ m, Safe.ClockFree (N1 m) := fun m _ _ ⟨h1, h2⟩ => ⟨hHc _ _ h1, h2⟩
    have n1 : Frag o [.assign "jneed" (Syntax.v "jrem")] (fun u => Hd A J st s0 u ∧
        eval u (.cmp .equal (.var "jrem") (.const 0)) = some 0) (N1 (J.length - st.pos)) :=
      set_frag o (E := .var "jrem") rfl (hN1c _) fun u ⟨hu, _⟩ => ⟨_, by simp only [eval]; exact hu.jrem,
        kept_has hu.kept (h.bound "jneed" (by decide)), hd_set hu (by decide) (by decide) _,
        by simp [setL, setLocal]⟩
    obtain ⟨m, hm⟩ : ∃ m, m = min (J.length - st.pos) maxFrame := ⟨_, rfl⟩
    have hev2 : ∀ u, N1 (J.length - st.pos) u → eval u (.cmp .less (.const (BitVec.ofNat 64 maxFrame))
        (.var "jneed")) = some (bw (decide (maxFrame < J.length - st.pos))) := fun u hu =>
      eval_lt (by decide) (by omega) rfl (by simp only [eval]; exact hu.2)
    have n2 : Frag o [.ite (Syntax.eLt (Syntax.n maxFrame) (Syntax.v "jneed")) [.assign "jneed" (lit maxFrame)] []]
        (N1 (J.length - st.pos)) (N1 m) := by
      refine frag_ite o (C := .cmp .less (.const (BitVec.ofNat 64 maxFrame)) (.var "jneed")) rfl (hN1c _)
        (fun u hu => ⟨_, hev2 u hu⟩) ?_ (noDecl _ rfl) (frag_nil o fun u ⟨hu, h0⟩ => ?_) (noDecl _ rfl)
      · refine set_frag o (E := .op .add (.var "jz") (.const (BitVec.ofNat 64 maxFrame))) rfl (hN1c _)
          fun u ⟨hu, hne⟩ => ?_
        rw [hev2 u hu] at hne
        have hlt := bw_ne0 hne
        simp only [decide_eq_true_eq] at hlt
        refine ⟨BitVec.ofNat 64 maxFrame, by simp [eval, kept_jz h hu.1.kept], ⟨_, hu.2⟩,
          hd_set hu.1 (by decide) (by decide) _, ?_⟩
        rw [hm, Nat.min_eq_right (by omega)]; simp [setL, setLocal]
      · rw [hev2 u hu] at h0
        have hlt := bw_eq0 h0
        simp only [decide_eq_false_iff_not] at hlt
        rw [hm, Nat.min_eq_left (by omega)]; exact hu
    have hev3 : ∀ u, N1 m u → eval u (.cmp .less (.op .add (.var "jb") (.var "jwl")) (.op .add (.var "jp")
        (.var "jneed"))) = some (bw (decide (st.base + st.len < st.pos + m))) := fun u hu =>
      eval_lt (by omega) (by omega)
        (eval_add (by simp only [eval]; exact hu.1.jb) (by simp only [eval]; exact hu.1.jwl))
        (eval_add (by simp only [eval]; exact hu.1.jp) (by simp only [eval]; exact hu.2))
    refine frag_append (xs := [_]) n1 (frag_append (xs := [_]) n2 (frag_ite o (C := .cmp .less (.op .add (.var "jb")
      (.var "jwl")) (.op .add (.var "jp") (.var "jneed"))) rfl hSc (fun u hu => ⟨_, hev3 u hu⟩) ?_ (noDecl _ rfl) ?_
      (noDecl _ rfl)))
    · -- octets wanted
      refine frag_pure (st.base + st.len < st.pos + m) (fun u ⟨hu, hne⟩ => by
        rw [hev3 u hu] at hne; simpa using bw_ne0 hne) (lowKK_want hfl) fun hwm => ?_
      have hw : st.base + st.len < st.pos + min (J.length - st.pos) maxFrame := by rw [← hm]; exact hwm
      refine frag_conseq (want_frag o h hfl hfd hpos hw) (fun u hu => hu.1.1) fun u hu => ⟨hu.1, ?_⟩
      simp only [stepSpec, if_neg (show ¬ J.length ≤ st.pos by omega), if_pos hw, OutAt]
      exact hu.2
    · -- the frame read
      refine frag_pure (¬ st.base + st.len < st.pos + m) (fun u ⟨hu, h0⟩ => by
        rw [hev3 u hu] at h0; simpa using bw_eq0 h0) (lowKK_read hfl) fun hwm => ?_
      have hw : ¬ st.base + st.len < st.pos + min (J.length - st.pos) maxFrame := by rw [← hm]; exact hwm
      refine frag_conseq (P0 := Hd A J st s0) ?_ (fun u hu => hu.1.1) fun _ h => h
      refine frag_append (frame_frag o h hfl hfd hpos hw) (frag_append (xs := [_]) (rec_frag o h hfl hfd hpos hw) ?_)
      have hne : J.drop st.pos ≠ [] := fun e => by
        have := congrArg List.length e; simp at this; omega
      have hev4 : ∀ u, RcDone A J st s0 u → eval u (.var "jwhy") =
          some (BitVec.ofNat 64 (whyOf (next spec st.key st.pos (J.drop st.pos)))) := fun u hu => by
        simp only [eval]; exact hu.why
      cases hnx : next spec st.key st.pos (J.drop st.pos) with
      | done =>
        rw [next_fault _ _ hne] at hnx
        split at hnx
        · cases hnx
        · split at hnx <;> cases hnx
      | bad why =>
        have hw0 : whyOf (Next.bad why) ≠ 0 := by cases why <;> decide
        refine frag_ite o (C := .var "jwhy") rfl hSc (fun u hu => ⟨_, hev4 u hu⟩)
          (frag_conseq (stopped_frag o h hfl hfd hpos hw hnx) (fun u hu => hu.1) fun u hu => ⟨hu.1, ?_⟩)
          (fun _ _ _ _ hy => by rw [show declared (ScanProg.stopped fail) = [] from rfl] at hy; cases hy)
          (frag_unsat lowKK_accept fun u ⟨hu, h0⟩ => by
            rw [hev4 u hu, hnx] at h0
            have := congrArg BitVec.toNat (Option.some.inj h0)
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by cases why <;> decide)] at this
            exact hw0 this) (noDecl _ rfl)
        have hs : stepSpec J st = .stop (stop spec st.pos (J.drop st.pos) st.key why) := by
          simp only [stepSpec, if_neg (show ¬ J.length ≤ st.pos by omega), if_neg hw, hnx]
        rw [hs]; exact hu.2
      | record rec taken rest =>
        refine frag_ite o (C := .var "jwhy") rfl hSc (fun u hu => ⟨_, hev4 u hu⟩)
          (frag_unsat (lowKK_stopped hfl) fun u ⟨hu, hne'⟩ => hne' (by rw [hev4 u hu, hnx]; rfl))
          (fun _ _ _ _ hy => by rw [show declared (ScanProg.stopped fail) = [] from rfl] at hy; cases hy)
          (frag_conseq (accept_frag o h hpos hw hnx) (fun u hu => hu.1) fun u hu => ⟨hu.1, ?_⟩) (noDecl _ rfl)
        have hs : stepSpec J st = if !st.acc.isEmpty && rec.key.isSome then .stop (.corrupt st.pos .formatAgain)
            else .record rec { st with pos := st.pos + taken, key := st.key <|> rec.key, acc := rec :: st.acc } := by
          simp only [stepSpec, if_neg (show ¬ J.length ≤ st.pos by omega), if_neg hw, hnx]
        rw [hs]; exact hu.2

/-! ## Steps chained, and the kernel -/

/-- **The window filled** after a want: with `m` more octets of the journal after the window's, its length set
and the rest of the area as it was, the area holds the state with them. -/
theorem areaAt_fill {A : Word} {J : Bytes} {st : St} {u u' : PancakeState σ} (h : AreaAt A J st u) {m : Nat}
    (hd : u'.memaddrs = u.memaddrs) (hb : u'.be = u.be)
    (hw : ∀ x ∈ [sSize, sBase, sPos, sKeyed, sCount], u'.memory (at_ A x) = u.memory (at_ A x))
    (hlen : u'.memory (at_ A sLen) = BitVec.ofNat 64 (st.len + m))
    (hkey : ∀ j, j < 16 → memLoadByte u'.memory u'.memaddrs u'.be (at_ A (sKey + j)) =
      memLoadByte u.memory u.memaddrs u.be (at_ A (sKey + j)))
    (hold : ∀ i, i < st.len → memLoadByte u'.memory u'.memaddrs u'.be (at_ A (sWindow + i)) =
      memLoadByte u.memory u.memaddrs u.be (at_ A (sWindow + i)))
    (hnew : ∀ i, st.len ≤ i → i < st.len + m →
      memLoadByte u'.memory u'.memaddrs u'.be (at_ A (sWindow + i)) = some (J.getD (st.base + i) 0)) :
    AreaAt A J (st.fill m) u' where
  size := by rw [hw sSize (by simp)]; exact h.size
  base := by rw [hw sBase (by simp)]; exact h.base
  len := hlen
  pos := by rw [hw sPos (by simp)]; exact h.pos
  keyed := by rw [hw sKeyed (by simp)]; exact h.keyed
  count := by rw [hw sCount (by simp)]; exact h.count
  window := fun i hi => by
    simp only [St.fill] at hi ⊢
    by_cases e : i < st.len
    · rw [hold i e]; exact h.window i e
    · exact hnew i (by omega) hi
  key := fun k hk => by
    rw [← h.key k hk, hd, hb]
    refine readByteArray_congr 16 _ fun j hj => ?_
    have e := hkey j hj
    rw [hd, hb, ← at_add] at e
    exact e

/-- The kernel's entry: the area at `A`, aligned and addressable, holding a state of reading `J` that keeps its
window, its address in `jsc`. -/
structure KernelIn (A : Word) (J : Bytes) (st : St) (e : PancakeState σ) : Prop where
  hA : A.toNat % 8 = 0
  dom : Dom A e.memaddrs
  sp : e.locals "jsc" = some A
  area : AreaAt A J st e
  valid : Valid J st
  short : J.length < 2 ^ 62

/-- After declarations from `e`: its memory, `jsc`, `jz` zero, and each of `ns` zero. -/
def ZAt (A : Word) (e : PancakeState σ) (ns : List String) (u : PancakeState σ) : Prop :=
  u.memory = e.memory ∧ u.memaddrs = e.memaddrs ∧ u.be = e.be ∧ u.locals "jsc" = some A ∧
    u.locals "jz" = some 0 ∧ ∀ y ∈ ns, u.locals y = some 0

/-- Locals declared, each set to `jz`. -/
theorem zeros_frag (o : Oracle σ) {A : Word} {e : PancakeState σ} : ∀ (ns pre : List String),
    (∀ y ∈ ns, y ≠ "jsc" ∧ y ≠ "jz") →
    Frag o (ns.map (.dec · (Syntax.v "jz"))) (ZAt A e pre) (ZAt A e (ns ++ pre))
  | [], _, _ => frag_nil o fun _ h => h
  | y :: ns, pre, h => by
    have hy := h y (List.mem_cons_self ..)
    refine frag_append (xs := [_]) (frag_dec o (E := .var "jz") rfl (P' := ZAt A e (y :: pre)) fun s hs => ?_)
      (frag_conseq (zeros_frag o ns (y :: pre) fun z hz => h z (List.mem_cons_of_mem _ hz)) (fun _ h => h)
        fun u hu => ⟨hu.1, hu.2.1, hu.2.2.1, hu.2.2.2.1, hu.2.2.2.2.1, fun z hz => hu.2.2.2.2.2 z (by
          simp only [List.mem_append, List.mem_cons] at hz ⊢
          rcases hz with (hz | hz) | hz
          · exact Or.inr (Or.inl hz)
          · exact Or.inl hz
          · exact Or.inr (Or.inr hz))⟩)
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hs
    refine ⟨0, by simp only [eval]; exact h5, h1, h2, h3, by simp [setLocal, Ne.symm hy.1, h4],
      by simp [setLocal, Ne.symm hy.2, h5], fun z hz => ?_⟩
    simp only [List.mem_cons] at hz
    by_cases ez : z = y
    · simp [setLocal, ez]
    · simp only [setLocal, if_neg ez]
      exact h6 z (hz.resolve_left ez)

/-- The step's locals are not `jsc` or `jz`. -/
theorem locals_apart : ScanProg.locals.all (fun y => y != "jsc" && y != "jz") = true := by decide +kernel

/-- **The kernel's declarations** give the step its premises. -/
theorem decls_frag (o : Oracle σ) {A : Word} {J : Bytes} {st : St} {e : PancakeState σ} (h : KernelIn A J st e) :
    Frag o ScanProg.decls (Like e)
      (fun u => StepIn A J st u ∧ u.memory = e.memory ∧ u.memaddrs = e.memaddrs ∧ u.be = e.be) := by
  refine frag_append (xs := [_]) (frag_dec o (E := .op .sub (.var "jsc") (.var "jsc")) rfl (P' := ZAt A e [])
    fun s hs => ⟨0, by simp [eval, hs.locals, h.sp], hs.memory, hs.memaddrs, hs.be,
      by simp [setLocal, hs.locals, h.sp], by simp [setLocal], fun _ hz => (nomatch hz)⟩)
    (frag_conseq (zeros_frag o ScanProg.locals [] fun y hy => by
      simpa only [Bool.and_eq_true, bne_iff_ne] using List.all_eq_true.mp locals_apart y hy) (fun _ h => h)
      fun u hu => ?_)
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hu
  have hdom : Dom A u.memaddrs := by rw [h2]; exact h.dom
  have harea := areaAt_keep h.hA h.area h.valid.len h2 h3 fun x _ _ _ => by rw [h1]
  exact ⟨⟨h.hA, hdom, h4, h5, harea, h.valid, h.short, fun y hy => ⟨0, h6 y (by simpa using hy)⟩⟩, h1, h2, h3⟩

theorem lowKK_head {fail : List Syntax.PStmt} (hfl : LowKK fail) : LowKK (ScanProg.stepHead fail) :=
  lowKK_append (xs := [_, _, _]) (lowK_any _ (k := .skip) (c := _) rfl) (lowKK_append (xs := [_])
    (lowKK_ite rfl hfl (fun k => ⟨k, rfl⟩)) (lowK_any _ (k := .skip) (c := _) rfl))

theorem lowKK_step {fail : List Syntax.PStmt} (hfl : LowKK fail) : LowKK (ScanProg.stepWith fail) :=
  lowKK_append (lowKK_head hfl) (lowKK_ite rfl (lowK_any _ (k := .skip) (c := _) rfl)
    (lowKK_append (xs := [_]) (lowK_any _ (k := .skip) (c := _) rfl) (lowKK_append (xs := [_])
      (lowK_any _ (k := .skip) (c := _) rfl) (lowKK_ite rfl (lowKK_want hfl) (lowKK_read hfl)))))

/-- **The kernel's step is `stepSpec`**: if it goes on, from its entry, its declarations and the step leave the
status `stepSpec` gives and what goes with it, the memory but the area as it was. -/
theorem kernel_frag (o : Oracle σ) {A : Word} {J : Bytes} {st : St} {e : PancakeState σ} (h : KernelIn A J st e)
    {fail : List Syntax.PStmt} (hfl : LowKK fail) (hfd : declared fail = []) :
    Frag o (ScanProg.decls ++ ScanProg.stepWith fail) (Like e) (fun u => OutAt A J st (stepSpec J st) u ∧
      (∀ a, ¬ AreaW A a → u.memory a = e.memory a) ∧ u.memaddrs = e.memaddrs ∧ u.be = e.be) :=
  frag_append (decls_frag o h) (frag_each o (lowKK_step hfl) fun _ hs => frag_conseq (step_frag o hs.1 hfl hfd)
    (fun _ h => h) fun _ hu => ⟨hu.2, fun a ha => (hu.1.memory a ha).trans (congrFun hs.2.1 a),
      hu.1.memaddrs.trans hs.2.2.1, hu.1.be.trans hs.2.2.2⟩)

/-! ## The premises can hold -/

section Witness

theorem valid_witness : Valid [] St.start := ⟨Nat.le_refl _, Nat.le_refl _, Nat.zero_le _, Nat.zero_le _,
  (fun h => by cases h), Nat.le_refl _⟩

theorem areaAt_witness : AreaAt 0 [] St.start zState where
  size := by decide
  base := by decide
  len := by decide
  pos := by decide
  keyed := by decide
  count := by decide
  window := fun i hi => absurd hi (Nat.not_lt_zero _)
  key := fun _ h => by cases h

theorem stepIn_witness : StepIn 0 [] St.start zState where
  hA := by decide
  dom := dom_witness
  sp := rfl
  jz := rfl
  area := areaAt_witness
  valid := valid_witness
  short := by decide
  bound := fun y _ => zBound y

/-- A keyed state: one record read, the journal's one octet in the window, the key all zeros. -/
def kSt : St := ⟨0, 1, 1, some (List.replicate 16 0), [.start]⟩

/-- Its area: the journal's length, the window's, where the next frame starts, keyed, one record. -/
def kMem (a : Word) : Word :=
  if a = at_ 0 sSize ∨ a = at_ 0 sLen ∨ a = at_ 0 sPos ∨ a = at_ 0 sKeyed ∨ a = at_ 0 sCount then 1 else 0

def kState : PancakeState Unit := { zState with memory := kMem }

theorem valid_keyed : Valid [0] kSt := ⟨by decide, by decide, by decide, by decide, fun _ => List.cons_ne_nil _ _,
  by decide⟩

theorem areaAt_keyed : AreaAt 0 [0] kSt kState where
  size := by decide
  base := by decide
  len := by decide
  pos := by decide
  keyed := by decide
  count := by decide
  window := fun i hi => by
    obtain rfl : i = 0 := by simp only [kSt] at hi; omega
    decide
  key := fun _ hk => by cases hk; decide

theorem stepIn_keyed : StepIn 0 [0] kSt kState where
  hA := by decide
  dom := dom_witness
  sp := rfl
  jz := rfl
  area := areaAt_keyed
  valid := valid_keyed
  short := by decide
  bound := fun y _ => zBound y

/-- A keyed state on the read path: one record read, the frame at 1 torn, the journal's two octets in the window. -/
def tSt : St := ⟨0, 2, 1, some (List.replicate 16 0), [.start]⟩

def tMem (a : Word) : Word :=
  if a = at_ 0 sSize ∨ a = at_ 0 sLen then 2 else
  if a = at_ 0 sPos ∨ a = at_ 0 sKeyed ∨ a = at_ 0 sCount then 1 else 0

def tState : PancakeState Unit := { zState with memory := tMem }

theorem areaAt_torn : AreaAt 0 [0, 0] tSt tState where
  size := by decide
  base := by decide
  len := by decide
  pos := by decide
  keyed := by decide
  count := by decide
  window := fun i hi => by
    simp only [tSt] at hi
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> decide
  key := fun _ hk => by cases hk; decide

theorem stepIn_torn : StepIn 0 [0, 0] tSt tState where
  hA := by decide
  dom := dom_witness
  sp := rfl
  jz := rfl
  area := areaAt_torn
  valid := ⟨by decide, by decide, by decide, by decide, fun _ => List.cons_ne_nil _ _, by decide⟩
  short := by decide
  bound := fun y _ => zBound y

theorem stepSpec_torn : stepSpec [0, 0] tSt = .stop (.torn 1) := rfl

theorem kernelIn_witness : KernelIn 0 [0, 0] tSt tState :=
  ⟨by decide, dom_witness, rfl, areaAt_torn, stepIn_torn.valid, by decide⟩

theorem hd_witness : Hd 0 [] St.start zState zState :=
  ⟨kept_refl _ _ _, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem tail_witness : Tail 0 [] 0 0 zState [] zState :=
  ⟨kept_refl _ _ _, fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => (nomatch h), fun _ h => (nomatch h),
    Nat.zero_le _, fun _ _ _ _ => rfl⟩

theorem vals_witness : Vals zState [] := fun _ h => (nomatch h)

theorem ctx_witness : Ctx 0 [] St.start zState [] zState := ⟨kept_refl _ _ _, areaAt_witness, vals_witness⟩

theorem tornAt_witness : TornAt 0 [] St.start zState [] [] 0
    (setL (setL zState "jtorn" (bw true)) "jq" (BitVec.ofNat 64 1)) :=
  ⟨⟨kept_set (kept_set (kept_refl _ _ _) (by decide) _) (by decide) _, { areaAt_witness with }, fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> rfl⟩, Nat.zero_le _⟩

theorem fwDone_witness : FwDone 0 [] St.start zState (setL zState "jwhy" (BitVec.ofNat 64 1)) where
  kept := kept_set (kept_refl _ _ _) (by decide) _
  area := { areaAt_witness with }
  vals := fun q hq => by
    simp only [fixedV, St.start, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  why := rfl
  len := fun h => by simp [fault, headerLength] at h
  type := fun h => by simp [fault, headerLength] at h

theorem rcDone_witness : RcDone 0 [] St.start zState zState where
  kept := kept_refl _ _ _
  area := areaAt_witness
  vals := fun q hq => by
    simp only [fixedV, St.start, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  why := rfl
  record := fun _ _ _ e => by simp [next] at e

theorem accAt_witness : AccAt 0 zState false [] [] zState :=
  ⟨kept_refl _ _ _, fun _ h => (nomatch h), fun _ h => (nomatch h), fun _ _ _ _ _ => rfl, fun h => by cases h⟩

theorem commitAt_witness : CommitAt 0 0 [] ⟨0, [], [], 0, 0, 0⟩ zState :=
  ⟨by decide, by decide, by decide, by decide, fun _ h => absurd h (Nat.not_lt_zero _), by decide, by decide,
    by decide⟩

end Witness

end DN.News.ScanRun
