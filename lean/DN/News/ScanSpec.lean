-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.ScanRun

/-!
# DN.News.ScanSpec

The scanner's step as a function of what it keeps between steps (`St`): the journal's end, octets wanted
after the window moved to the next frame, a record read, or reading stopped (`stepSpec`). Steps, a host
giving after each want at least one and at most the octets wanted, read the journal as `Journal.scan`
does, within one step more than twice its length (`drive_scan`).
-/

namespace DN.News.ScanRun

open DN.News.Journal
open DN.News.ScanProg (chunk windowMax whyCode)

/-- What the scanner keeps between steps: its window `J[base, base + len)` of the journal `J`, where the
next frame starts, the journal's key once read, and the records read, the last first. -/
structure St where
  base : Nat
  len : Nat
  pos : Nat
  key : Option Bytes
  acc : List Record

/-- What a step does: the journal ends cleanly, octets are wanted after the window moved to the next
frame, a record is read, or reading stops. -/
inductive Out
  | clean
  | want (st : St) (n : Nat)
  | record (rec : Record) (st : St)
  | stop (e : End)

/-- **A step**, as the scanner takes it: the frame at `pos` is read once the window holds it, or as much of
the journal as is left, up to a frame's largest size. -/
def stepSpec (J : Bytes) (st : St) : Out :=
  if J.length ≤ st.pos then .clean
  else if st.base + st.len < st.pos + min (J.length - st.pos) maxFrame then
    .want { st with base := st.pos, len := st.base + st.len - st.pos } (min chunk (J.length - (st.base + st.len)))
  else match next spec st.key st.pos (J.drop st.pos) with
    | .record rec taken _ =>
      if !st.acc.isEmpty && rec.key.isSome then .stop (.corrupt st.pos .formatAgain)
      else .record rec { st with pos := st.pos + taken, key := st.key <|> rec.key, acc := rec :: st.acc }
    | .bad why => .stop (stop spec st.pos (J.drop st.pos) st.key why)
    | .done => .clean

/-- `m` more octets of the journal in the window. -/
def St.fill (st : St) (m : Nat) : St := { st with len := st.len + m }

/-- Steps, a host giving after each want `pick` octets: what reading ends with, if it ends within `f`
steps. A function of the state is any host, as no state comes twice: what is left falls each step. -/
def drive (J : Bytes) (pick : St → Nat → Nat) : Nat → St → Option Scan
  | 0, _ => none
  | f + 1, st =>
    match stepSpec J st with
    | .clean => some ⟨st.acc.reverse, .clean⟩
    | .stop e => some ⟨st.acc.reverse, e⟩
    | .record _ st' => drive J pick f st'
    | .want st' n => drive J pick f (st'.fill (pick st' n))

/-- What a scanner's state keeps: the window within the journal and starting at or before the next
frame, the key known only once a record is read. -/
structure Valid (J : Bytes) (st : St) : Prop where
  base : st.base ≤ st.pos
  pos : st.pos ≤ st.base + st.len
  stop : st.base + st.len ≤ J.length
  len : st.len ≤ windowMax
  keyed : st.key.isSome → st.acc ≠ []
  count : st.acc.length ≤ st.pos

/-- A frame that checks: its length within the journal's rest, its payload within the largest. -/
theorem fault_none {key : Option Bytes} {q : Nat} {bs : Bytes} (h : fault key q bs = none) :
    13 + readLE (bs.take 4) + 1 ≤ bs.length ∧ readLE (bs.take 4) ≤ maxPayload := by
  unfold fault at h
  simp only [headerLength] at h
  split at h; · cases h
  split at h; · cases h
  split at h; · cases h
  rename_i h1 h2 h3
  exact ⟨by omega, by omega⟩

theorem next_record {key : Option Bytes} {off : Nat} {bs : Bytes} {rec : Record} {taken : Nat} {rest : Bytes}
    (h : next spec key off bs = .record rec taken rest) :
    rest = bs.drop taken ∧ headerLength + 1 ≤ taken ∧ taken ≤ bs.length ∧ taken ≤ maxFrame := by
  cases bs with
  | nil => simp [next] at h
  | cons b bs' =>
    rw [next_fault _ _ (List.cons_ne_nil _ _)] at h
    have hf := fault_ne key off (b :: bs')
    revert h hf
    cases hfa : fault key off (b :: bs') with
    | some w => intro h; cases h
    | none =>
      intro h _
      cases hr : recordOf spec (typeOf (b :: bs')) (payloadOf (b :: bs')) with
      | none => rw [hr] at h; cases h
      | some r =>
        rw [hr] at h
        simp only [Next.record.injEq] at h
        obtain ⟨_, rfl, rfl⟩ := h
        obtain ⟨h1, h2⟩ := fault_none hfa
        refine ⟨rfl, ?_, ?_, ?_⟩ <;> simp only [headerLength, maxFrame, maxPayload] at h1 h2 ⊢ <;> omega

/-- Whether a frame that checks under `k` starts at any of the `n` places from `q`. -/
def seen (J k : Bytes) (q n : Nat) : Bool := (List.range n).any fun j => checks spec k (q + j) (J.drop (q + j))

theorem seen_succ (J k : Bytes) (q n : Nat) :
    seen J k q (n + 1) = (seen J k q n || checks spec k (q + n) (J.drop (q + n))) := by
  simp [seen, List.range_succ, List.any_append]

/-- **`anyChecks` over the journal from `q`** looks at each place from `q` to its end. -/
theorem anyChecks_seen (J k : Bytes) : ∀ (n q : Nat), J.length - q = n →
    anyChecks spec k q (J.drop q) = seen J k q n
  | 0, q, h => by
    rw [List.drop_eq_nil_of_le (by omega)]; simp [anyChecks, seen]
  | n + 1, q, h => by
    rw [List.drop_eq_getElem_cons (by omega), anyChecks, ← List.drop_eq_getElem_cons (by omega),
      anyChecks_seen J k n (q + 1) (by omega)]
    simp only [seen, List.range_succ_eq_map, List.any_cons, List.any_map, Nat.add_zero]
    congr 2
    funext j
    simp only [Function.comp_apply]
    rw [show q + (j + 1) = q + 1 + j by omega]

/-- What is left to read and to fill: each step that does not end makes it smaller. -/
def St.left (J : Bytes) (st : St) : Nat := (J.length - st.pos) + (J.length - (st.base + st.len))

theorem window_room : maxFrame + chunk ≤ windowMax := by decide

/-- **After octets wanted**, as many as the host gives, at least one and at most those wanted, the state keeps its
window and less is left. -/
theorem valid_want {J : Bytes} {st st' : St} {n : Nat} (hv : Valid J st) (h : stepSpec J st = .want st' n) :
    0 < n ∧ ∀ m, 0 < m → m ≤ n → Valid J (st'.fill m) ∧ (st'.fill m).left J < st.left J := by
  simp only [stepSpec] at h
  split at h
  · cases h
  split at h
  · simp only [Out.want.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hw := window_room
    have := hv.pos
    have := hv.stop
    refine ⟨by simp only [Nat.lt_min, chunk]; omega, fun m hm0 hmn => ?_⟩
    have hmn' := Nat.le_trans hmn (Nat.min_le_right _ _)
    have hmc := Nat.le_trans hmn (Nat.min_le_left _ _)
    refine ⟨⟨Nat.le_refl _, ?_, ?_, ?_, hv.keyed, hv.count⟩, ?_⟩ <;> simp only [St.fill, St.left] <;> omega
  · split at h
    · split at h <;> cases h
    · cases h
    · cases h

/-- **After a record read**, the state keeps its window, less is left, and the next frame starts later. -/
theorem valid_record {J : Bytes} {st st' : St} {rec : Record} (hv : Valid J st) (h : stepSpec J st = .record rec st') :
    Valid J st' ∧ st'.left J < st.left J ∧ J.length - st'.pos < J.length - st.pos := by
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
    · simp only [Out.record.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨-, ht1, ht2, ht3⟩ := next_record hnx
      simp only [List.length_drop] at ht2
      simp only [headerLength] at ht1
      have := hv.base
      have := hv.stop
      have := hv.count
      refine ⟨⟨?_, ?_, hv.stop, hv.len, fun _ => List.cons_ne_nil _ _, ?_⟩, ?_, ?_⟩ <;>
        simp only [St.left, List.length_cons] at * <;> omega
  · cases h
  · cases h

/-- **Steps read the journal as `scanFrom` does**: from a state that keeps its window, with a host that
gives after each want at least one and at most the octets wanted, reading ends within one step more than
is left, as `scanFrom` with fuel enough ends. -/
theorem drive_scanFrom (J : Bytes) {pick : St → Nat → Nat} (hp : ∀ st n, 0 < n → 0 < pick st n ∧ pick st n ≤ n) :
    ∀ (f : Nat) (st : St) (F : Nat), Valid J st → st.left J < f → J.length - st.pos < F →
      drive J pick f st = some (scanFrom spec F (J.drop st.pos) st.pos st.key st.acc)
  | 0, _, _, _, hf, _ => absurd hf (Nat.not_lt_zero _)
  | f + 1, st, F, hv, hf, hF => by
    obtain ⟨F, rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    simp only [drive, stepSpec]
    by_cases h1 : J.length ≤ st.pos
    · rw [if_pos h1, List.drop_eq_nil_of_le h1]
      simp [scanFrom, next]
    rw [if_neg h1]
    by_cases h2 : st.base + st.len < st.pos + min (J.length - st.pos) maxFrame
    · rw [if_pos h2]
      have hs : stepSpec J st = .want { st with base := st.pos, len := st.base + st.len - st.pos }
          (min chunk (J.length - (st.base + st.len))) := by simp only [stepSpec, if_neg h1, if_pos h2]
      obtain ⟨hn, hk⟩ := valid_want hv hs
      obtain ⟨hm0, hmn⟩ := hp { st with base := st.pos, len := st.base + st.len - st.pos } _ hn
      obtain ⟨hv', hl⟩ := hk _ hm0 hmn
      exact drive_scanFrom J hp f _ (F + 1) hv' (by omega) hF
    rw [if_neg h2]
    simp only [scanFrom]
    cases hnx : next spec st.key st.pos (J.drop st.pos) with
    | done => rfl
    | bad why => rfl
    | record rec taken rest =>
      obtain ⟨hrest, -⟩ := next_record hnx
      simp only [spec_formatOnce, Bool.true_and]
      by_cases h3 : (!st.acc.isEmpty && rec.key.isSome) = true
      · simp only [if_pos h3]
      · simp only [if_neg h3]
        rw [hrest, List.drop_drop]
        have hs : stepSpec J st = .record rec
            { st with pos := st.pos + taken, key := st.key <|> rec.key, acc := rec :: st.acc } := by
          simp only [stepSpec, if_neg h1, if_neg h2, hnx, if_neg h3]
        obtain ⟨hv', hl, hF'⟩ := valid_record hv hs
        exact drive_scanFrom J hp f _ F hv' (by omega) (by simp only at hF' ⊢; omega)

/-- The state reading starts in: an empty window at the journal's start, no key, no record. -/
def St.start : St := ⟨0, 0, 0, none, []⟩

/-- **Steps read the journal as `scan` does**, within one step more than twice its length, whatever
octets the host gives after each want, at least one and at most the octets wanted. -/
theorem drive_scan (J : Bytes) {pick : St → Nat → Nat} (hp : ∀ st n, 0 < n → 0 < pick st n ∧ pick st n ≤ n) :
    drive J pick (2 * J.length + 1) St.start = some (scan J) := by
  have := drive_scanFrom J hp (2 * J.length + 1) St.start (J.length + 1)
    ⟨Nat.le_refl _, Nat.le_refl _, Nat.zero_le _, Nat.zero_le _, (fun h => by cases h), Nat.le_refl _⟩
    (by simp only [St.left, St.start]; omega) (by simp only [St.start]; omega)
  rw [this]; rfl

/-- What a record read from a frame is: the frame checks, and its type and payload make the record. -/
theorem next_record_of {key : Option Bytes} {q : Nat} {bs : Bytes} {rec : Record} {taken : Nat} {rest : Bytes}
    (h : next spec key q bs = .record rec taken rest) : fault key q bs = none ∧
      Journal.recordOf spec (typeOf bs) (payloadOf bs) = some rec ∧ taken = 13 + readLE (bs.take 4) + 1 := by
  cases bs with
  | nil => simp [next] at h
  | cons b bs' =>
    rw [next_fault _ _ (List.cons_ne_nil _ _)] at h
    cases hf : fault key q (b :: bs') with
    | some w => rw [hf] at h; cases h
    | none =>
      rw [hf] at h
      cases hr : Journal.recordOf spec (typeOf (b :: bs')) (payloadOf (b :: bs')) with
      | none => rw [hr] at h; cases h
      | some r =>
        rw [hr] at h
        simp only [Next.record.injEq] at h
        obtain ⟨rfl, rfl, -⟩ := h
        exact ⟨rfl, rfl, by simp [headerLength]⟩

theorem record_key (r : Record) : r.key.isSome = decide (r.type = formatType) := by
  cases r <;> simp [Record.key, Record.type, formatType, commitType, startType]

theorem seen_mono (J k : Bytes) (q : Nat) : ∀ {i n : Nat}, i ≤ n → seen J k q i = true → seen J k q n = true
  | i, 0, hin, h => by have : i = 0 := by omega
                       subst this; simp [seen] at h
  | i, n + 1, hin, h => by
    rw [seen_succ]
    by_cases e : i = n + 1
    · subst e; rw [seen_succ] at h; exact h
    · rw [seen_mono J k q (n := n) (by omega) h, Bool.true_or]

theorem torn_code (w : Why) : decide (whyCode w < 5) = w.torn := by cases w <;> rfl

end DN.News.ScanRun
