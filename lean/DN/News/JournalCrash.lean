-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.FsModel
import DN.News.Journal

/-!
# DN.News.JournalCrash

The journal on the file system of `DN.News.FsModel`, as docs/decisions/0005-article-store.md says
the store writes it: a file created, or cut to nothing, takes its format, appended and synced; then
records are appended where those kept end, each synced before the next and each run's first a
start; after a crash, the next start syncs it and cuts away a torn tail, syncing the cut, or makes
it again when no format is left. Between operations it is in one of four states: `Creating` while
its format is written and `Unformatted` once a crash left it none, `Steady` once its format is kept
and `Found` once a crash left it so, before any cut.

Two things are assumed of what a crash leaves. Past a format kept, a frame whose tag checks under
the journal's key is one an append wrote where it lies (`Unforged`, computed by `unforged`): the tag
takes the key, which neither a crash's junk nor an article's author has, and the offset, so a frame
moved elsewhere does not check. At the start of a journal whose format is not kept, a frame that
checks under the key it carries is a format an append wrote there (`FormatWritten`): that key is
the frame's own, so this rests on the file system and the device showing no file another's octets
after a crash, and on junk making such a frame only by chance. A restart of the process while syncs
are trusted is a crash that loses nothing (`sync_after`); it needs only the assumption past the
format, of octets the program wrote. After a failed sync a restart is not covered, as Linux may
have marked as clean pages it could not write.

Proven: a crash reads, never as corruption, as the records kept and perhaps one more, written whole
where they end and allowed there (`steady_crash`), or, while the format is written, as nothing, a
torn tail at the start or a format a creation wrote (`creating_crash`); and the store's operations,
their failures, crashes and restarts keep the four states — after a record appended, only it can be
left whole where the records end (`steady_append`), and after the records kept are synced nothing
can (`steady_sync_same`); what a crash left is cut back to `Steady` or `Creating` (`found_cut`,
`unformatted_again`). Under them: a frame whose tag checks within what an append wrote is that
append's record whole (`frame_encode`), and a frame is its record's alone (`encode_inj`).
-/

namespace DN.News.JournalCrash

open DN.News.Journal
open DN.News.FsModel (Data leaves_exact leaves_seen)
open DN.News.CommandSpec (ascii)

/-! ## Frames whose tag checks -/

/-- Whether the frame at `offset`, the start of `bs`, is whole and its tag checks: under `key`, or,
with none, under the key it carries the way the format does. -/
def tagged (key : Option Bytes) (offset : Nat) (bs : Bytes) : Bool :=
  match next spec key offset bs with
  | .record .. | .bad .notARecord => true
  | _ => false

/-- The frame at the start of `bs`, as long as its length says. -/
def frameOf (bs : Bytes) : Bytes := bs.take (headerLength + readLE (bs.take 4) + 1)

theorem tagged_nil (key : Option Bytes) (offset : Nat) : tagged key offset [] = false := by
  simp [tagged, next]

theorem next_done (r : Rules) (key : Option Bytes) (offset : Nat) (bs : Bytes)
    (h : next r key offset bs = .done) : bs = [] := by
  cases bs with
  | nil => rfl
  | cons b bs =>
    unfold next at h
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at h
    repeat' split at h
    all_goals cases h

theorem next_formatAgain (r : Rules) (key : Option Bytes) (offset : Nat) (bs : Bytes) :
    next r key offset bs ≠ .bad .formatAgain := by
  intro h
  unfold next at h
  dsimp only at h
  repeat' split at h
  all_goals cases h

/-- A frame whose tag checks is whole: as long as its length says. -/
theorem tagged_whole (key : Option Bytes) (offset : Nat) (bs : Bytes)
    (h : tagged key offset bs = true) : headerLength + readLE (bs.take 4) + 1 ≤ bs.length := by
  refine Nat.le_of_not_lt fun hlt => ?_
  have ha : atLeast (headerLength + readLE (bs.take 4) + 1) bs = false := atLeast_of_lt _ _ hlt
  have hn : next spec key offset bs = .done ∨ next spec key offset bs = .bad .short ∨
      next spec key offset bs = .bad .tooLong := by
    unfold next
    dsimp only
    simp only [ha, Bool.not_false, ↓reduceIte]
    repeat' split
    all_goals simp
  rcases hn with hn | hn | hn <;> simp [tagged, hn] at h

/-- What does not check is the end of the journal, or fails for a reason a torn append can leave. -/
theorem tagged_false (key : Option Bytes) (offset : Nat) (bs : Bytes)
    (h : tagged key offset bs = false) :
    next spec key offset bs = .done ∨ ∃ w, next spec key offset bs = .bad w ∧ w.torn = true := by
  unfold tagged at h
  have hf := next_formatAgain spec key offset bs
  generalize next spec key offset bs = n at h hf
  rcases n with _ | ⟨_, _, _⟩ | ⟨_ | _ | _ | _ | _ | _⟩ <;> simp_all [Why.torn]

/-- What `checks` asks is whether the frame is tagged under the journal's key. -/
theorem checks_tagged (k : Bytes) (offset : Nat) (bs : Bytes) :
    checks spec k offset bs = tagged (some k) offset bs := rfl

/-- No frame that checks starts anywhere in `bs` if none starts at any of its octets. -/
theorem anyChecks_false (k : Bytes) :
    ∀ (bs : Bytes) (offset : Nat),
      (∀ i, i < bs.length → tagged (some k) (offset + i) (bs.drop i) = false) →
      anyChecks spec k offset bs = false
  | [], _, _ => rfl
  | b :: bs, offset, h => by
    have h0 := h 0 (by simp)
    have ht := anyChecks_false k bs (offset + 1) fun i hi => by
      have := h (i + 1) (by simp; omega)
      rw [show offset + (i + 1) = offset + 1 + i by omega] at this
      simpa using this
    simp only [Nat.add_zero, List.drop_zero] at h0
    simp only [anyChecks, checks_tagged, h0, ht, Bool.or_self]

/-! ## Records by their frames -/

/-- A record's frame starts with its payload's length. -/
theorem encode_take4 (r : Record) (k : Bytes) (offset : Nat) :
    (r.encode k offset).take 4 = le 4 r.payload.length := by
  rw [← List.append_nil (r.encode k offset), encode_shape, List.append_assoc]
  exact List.take_left' (le_length _ _)

theorem payload_lt (r : Record) (h : r.ok = true) : r.payload.length < 256 ^ 4 := by
  have := payload_length r h
  simp only [maxPayload] at this
  omega

/-- **A whole frame within what an append wrote is that append's record, whole**: its length is
the record's, so it is all of the record's frame. -/
theorem frame_encode (bs w : Bytes) (r : Record) (hr : r.ok = true) (k : Bytes) (offset : Nat)
    (hl : headerLength + readLE (bs.take 4) + 1 ≤ bs.length) (hf : frameOf bs <+: w)
    (hw : w <+: r.encode k offset) : r.encode k offset <+: bs ∧ r.encode k offset <+: w := by
  have hp := hf.trans hw
  have hlen : (frameOf bs).length = headerLength + readLE (bs.take 4) + 1 := by
    simp only [frameOf, List.length_take]; omega
  have h4 : bs.take 4 = le 4 r.payload.length := by
    have e1 : (frameOf bs).take 4 = bs.take 4 := by
      rw [frameOf, List.take_take, Nat.min_eq_left (by simp only [headerLength]; omega)]
    have e2 : (frameOf bs).take 4 = (r.encode k offset).take 4 := by
      rw [List.prefix_iff_eq_take.mp hp, List.take_take,
        Nat.min_eq_left (by rw [hlen]; simp only [headerLength]; omega)]
    rw [← e1, e2, encode_take4]
  have hn : headerLength + readLE (bs.take 4) + 1 = (r.encode k offset).length := by
    rw [h4, readLE_le _ _ (payload_lt r hr), encode_length]
  have heq : frameOf bs = r.encode k offset := by
    rw [List.prefix_iff_eq_take.mp hp, hlen, hn, List.take_length]
  refine ⟨?_, heq ▸ hf⟩
  rw [← heq]
  exact List.take_prefix _ _

/-- **A frame is its record's alone**: the type and the payload it holds give the record back. -/
theorem encode_inj (r r' : Record) (hr : r.ok = true) (hr' : r'.ok = true) (k k' : Bytes)
    (o o' : Nat) (h : r.encode k o = r'.encode k' o') : r = r' := by
  have hs := encode_shape r k o []
  have hs' := encode_shape r' k' o' []
  rw [List.append_nil] at hs hs'
  have hl : ∀ (q : Record) (key : Bytes) (off : Nat),
      (le 4 q.payload.length ++ le 8 (tagOf key off q.type q.payload)).length = 12 := by
    intro q key off; simp [le_length]
  have hd : (r.encode k o).drop 12 = (r'.encode k' o').drop 12 := by rw [h]
  rw [hs, hs', List.drop_left' (hl r k o), List.drop_left' (hl r' k' o')] at hd
  simp only [List.cons.injEq, List.append_cancel_right_eq] at hd
  have ht : r.type = r'.type := by
    rw [← type_toNat r, ← type_toNat r', hd.1]
  have := recordOf_payload r hr
  rw [ht, hd.2, recordOf_payload r' hr'] at this
  exact (Option.some.inj this).symm

/-- A record's frame that starts what another's holds is that other's. -/
theorem encode_prefix (r r' : Record) (hr : r.ok = true) (hr' : r'.ok = true) (k : Bytes)
    (o : Nat) (h : r'.encode k o <+: r.encode k o) : r' = r := by
  have hn : headerLength + readLE ((r'.encode k o).take 4) + 1 = (r'.encode k o).length := by
    rw [encode_take4, readLE_le _ _ (payload_lt r' hr'), encode_length]
  have hf : frameOf (r'.encode k o) = r'.encode k o := by
    rw [frameOf, hn, List.take_length]
  have h1 := (frame_encode (r'.encode k o) (r.encode k o) r hr k o (Nat.le_of_eq hn)
    (by rw [hf]; exact h) (List.prefix_refl _)).1
  have he : r.encode k o = r'.encode k o :=
    h1.eq_of_length (Nat.le_antisymm h1.length_le h.length_le)
  exact (encode_inj r r' hr hr' k k o o he).symm

/-! ## The journal grows at its end -/

theorem encodeFrom_append (k : Bytes) :
    ∀ (xs ys : List Record) (offset : Nat),
      encodeFrom k offset (xs ++ ys) =
        encodeFrom k offset xs ++ encodeFrom k (offset + (encodeFrom k offset xs).length) ys
  | [], ys, offset => by simp [encodeFrom]
  | x :: xs, ys, offset => by
    rw [List.cons_append, encodeFrom_cons, encodeFrom_cons,
      encodeFrom_append k xs ys (offset + (x.encode k offset).length), List.append_assoc]
    simp only [List.length_append, Nat.add_assoc]

/-- **A record appended at the journal's end** makes the journal of one more record. -/
theorem journal_append (k : Bytes) (rs : List Record) (r : Record) :
    journal k (rs ++ [r]) = journal k rs ++ r.encode k (journal k rs).length := by
  simp only [journal]
  rw [← List.cons_append, encodeFrom_append]
  simp [encodeFrom]

theorem journal_length (k : Bytes) (hk : k.length = keyLength) (rs : List Record) :
    firstFrame ≤ (journal k rs).length := by
  rw [journal_split, List.length_append, format_encode_length k hk]
  omega

theorem drop_after (xs ys : Bytes) (i : Nat) : (xs ++ ys).drop (xs.length + i) = ys.drop i := by
  simp [List.drop_append]

/-- **What follows the records**: nothing reads as the journal ending cleanly; anything else no
longer than the largest frame, with no frame that checks starting anywhere in it, as a torn tail
where it starts. -/
theorem scan_rest (k : Bytes) (hk : k.length = keyLength) (cs : List Record) (hcs : Appends cs)
    (t : Bytes) (ht : t.length ≤ maxFrame)
    (hq : ∀ i, i < t.length → tagged (some k) ((journal k cs).length + i) (t.drop i) = false) :
    scan (journal k cs ++ t) =
      ⟨.format k :: cs, if t.isEmpty then .clean else .torn (journal k cs).length⟩ := by
  cases t with
  | nil => simp [scan_encoded k hk cs hcs]
  | cons b t =>
    have h0 := hq 0 (by simp)
    simp only [Nat.add_zero, List.drop_zero] at h0
    rcases tagged_false _ _ _ h0 with hn | ⟨w, hn, hw⟩
    · exact absurd (next_done _ _ _ _ hn) (by simp)
    · rw [scan_stop k hk cs hcs _ w hn hw ht ?_]
      · simp
      · simp only [Quiet, List.tail_cons]
        exact anyChecks_false k t _ fun i hi => by
          have := hq (i + 1) (by simp; omega)
          rw [show (journal k cs).length + (i + 1) = (journal k cs).length + 1 + i by omega] at this
          simpa using this

/-! ## What a crash may leave -/

/-- **Assumed of what a crash leaves past a format kept**: past the octets the file kept, a frame
whose tag checks under the journal's key `k` is one an append wrote where it lies. The tag takes the
key, which neither a crash's junk nor an article's author has, and the offset. -/
def Unforged (k : Bytes) (d : Data) (c : Bytes) : Prop :=
  ∀ o, d.kept.length ≤ o → tagged (some k) o (c.drop o) = true →
    ∃ w, (o, w) ∈ d.written ∧ frameOf (c.drop o) <+: w

/-- **Assumed of what a crash leaves where no format is kept**: a frame at the start that checks
under the key it carries is a format an append wrote there. The key is the frame's own, so this
rests on the file system and the device showing no file another's octets after a crash, and on
junk making such a frame only by chance. -/
def FormatWritten (d : Data) (c : Bytes) : Prop :=
  tagged none 0 c = true → ∃ w, (0, w) ∈ d.written ∧ frameOf c <+: w

/-- `Unforged`, computed: no frame starts past the octets left, so finitely many offsets matter. -/
def unforged (k : Bytes) (d : Data) (c : Bytes) : Bool :=
  (List.range (c.length + 1)).all fun o =>
    !(decide (d.kept.length ≤ o) && tagged (some k) o (c.drop o)) ||
      d.written.any fun w => w.1 == o && (frameOf (c.drop o)).isPrefixOf w.2

/-- `FormatWritten`, computed. -/
def formatWritten (d : Data) (c : Bytes) : Bool :=
  !tagged none 0 c || d.written.any fun w => w.1 == 0 && (frameOf c).isPrefixOf w.2

theorem unforged_iff (k : Bytes) (d : Data) (c : Bytes) :
    unforged k d c = true ↔ Unforged k d c := by
  constructor
  · intro h o ho ht
    by_cases hoc : o ≤ c.length
    · have := List.all_eq_true.mp h o (List.mem_range.mpr (by omega))
      simp only [ho, decide_true, ht, Bool.and_self, Bool.not_true, Bool.false_or,
        List.any_eq_true, Bool.and_eq_true, beq_iff_eq, List.isPrefixOf_iff_prefix] at this
      obtain ⟨⟨o', w⟩, hm, rfl, hp⟩ := this
      exact ⟨w, hm, hp⟩
    · rw [List.drop_eq_nil_of_le (by omega), tagged_nil] at ht
      cases ht
  · intro h
    refine List.all_eq_true.mpr fun o _ => ?_
    cases hc : (decide (d.kept.length ≤ o) && tagged (some k) o (c.drop o))
    · simp
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨w, hm, hp⟩ := h o hc.1 hc.2
      simp only [Bool.not_true, Bool.false_or, List.any_eq_true, Bool.and_eq_true, beq_iff_eq,
        List.isPrefixOf_iff_prefix]
      exact ⟨(o, w), hm, rfl, hp⟩

theorem formatWritten_iff (d : Data) (c : Bytes) :
    formatWritten d c = true ↔ FormatWritten d c := by
  constructor
  · intro h ht
    simp only [formatWritten, ht, Bool.not_true, Bool.false_or, List.any_eq_true,
      Bool.and_eq_true, beq_iff_eq, List.isPrefixOf_iff_prefix] at h
    obtain ⟨⟨o, w⟩, hm, rfl, hp⟩ := h
    exact ⟨w, hm, hp⟩
  · intro h
    cases ht : tagged none 0 c
    · simp [formatWritten, ht]
    · obtain ⟨w, hm, hp⟩ := h ht
      simp only [formatWritten, ht, Bool.not_true, Bool.false_or, List.any_eq_true,
        Bool.and_eq_true, beq_iff_eq, List.isPrefixOf_iff_prefix]
      exact ⟨(0, w), hm, rfl, hp⟩

/-- Nothing left holds no frame. -/
theorem formatWritten_nil (d : Data) : FormatWritten d [] := by
  intro h
  rw [tagged_nil] at h
  cases h

/-- What a file holds after octets appended to it empty is what was appended there. -/
theorem formatWritten_append (d : Data) (hs : d.seen = []) (bs : Bytes) :
    FormatWritten (d.append bs) (d.append bs).seen := by
  intro _
  refine ⟨bs, ?_, ?_⟩
  · simp [Data.append, hs]
  · simp only [Data.append, hs, List.nil_append]
    exact List.take_prefix _ _

/-- Nothing past the octets kept holds no frame. -/
theorem unforged_kept (k : Bytes) (d : Data) (c : Bytes) (h : c.length ≤ d.kept.length) :
    Unforged k d c := by
  intro o ho ht
  rw [List.drop_eq_nil_of_le (by omega), tagged_nil] at ht
  cases ht

/-- **The journal while its format is written**: nothing of it kept, no more than the format's
frame, and appends only of formats, at its start. -/
structure Creating (d : Data) : Prop where
  kept : d.kept = []
  high : d.high ≤ firstFrame
  written : ∀ o w, (o, w) ∈ d.written →
    o = 0 ∧ ∃ k, k.length = keyLength ∧ w <+: (Record.format k).encode k 0

/-- **The journal once its format is kept**: the format under `k` and the records `rs` kept; no
more than the largest frame after them; every append made at or before where they end, and one past
the format the first part of a record, not a format, framed under `k` where it was made; and every
record an append wrote whole where they end, that a crash may leave there whole, one `P` allows. -/
structure Steady (k : Bytes) (rs : List Record) (P : Record → Prop) (d : Data) : Prop where
  key : k.length = keyLength
  records : Appends rs
  kept : d.kept = journal k rs
  high : d.high ≤ (journal k rs).length + maxFrame
  written : ∀ o w, (o, w) ∈ d.written → o ≤ (journal k rs).length ∧
    (0 < o → ∃ r : Record, r.ok = true ∧ r.key = none ∧ w <+: r.encode k o)
  back : ∀ w r, ((journal k rs).length, w) ∈ d.written → r.ok = true →
    r.encode k (journal k rs).length <+: w →
    (journal k rs).length + (r.encode k (journal k rs).length).length ≤ d.high → P r

/-- No append was made where the records `rs` under `k` end, nor past it. -/
def Fresh (k : Bytes) (rs : List Record) (d : Data) : Prop :=
  ∀ o w, (o, w) ∈ d.written → o < (journal k rs).length

theorem appends_snoc (rs : List Record) (hrs : Appends rs) (r : Record) (hr : r.ok = true)
    (hkey : r.key = none) : Appends (rs ++ [r]) := by
  intro q hq
  simp only [List.mem_append, List.mem_singleton] at hq
  rcases hq with hq | rfl
  · exact hrs q hq
  · exact ⟨hr, hkey⟩

/-- **A crash of the journal once its format is kept reads, without corruption, as the records
kept and, perhaps, one more**: a record an append wrote whole at their end, one `P` allows; the
journal ends cleanly where they do, or in a torn tail there. -/
theorem steady_crash (k : Bytes) (rs : List Record) (P : Record → Prop) (d : Data)
    (h : Steady k rs P d) (c : Bytes) (hc : d.Leaves c) (hu : Unforged k d c) :
    ∃ rs' t, c = journal k rs' ++ t ∧
      (rs' = rs ∨ ∃ r, P r ∧ r.ok = true ∧ r.key = none ∧ rs' = rs ++ [r]) ∧
      scan c = ⟨.format k :: rs', if t.isEmpty then .clean else .torn (journal k rs').length⟩ := by
  obtain ⟨hk, hrs, hkept, hhigh, hwr, hback⟩ := h
  obtain ⟨⟨g, hg⟩, hlen⟩ := hc
  rw [hkept] at hg
  subst hg
  have hx := journal_length k hk rs
  have hff : 0 < firstFrame := by decide
  have hno : ∀ o, (journal k rs).length < o →
      tagged (some k) o ((journal k rs ++ g).drop o) = false := by
    intro o ho
    cases htg : tagged (some k) o ((journal k rs ++ g).drop o) with
    | false => rfl
    | true =>
      obtain ⟨w, hw, _⟩ := hu o (by rw [hkept]; omega) htg
      have := (hwr o w hw).1
      omega
  have hafter : ∀ (cs : List Record) (t : Bytes),
      journal k rs ++ g = journal k cs ++ t → (journal k rs).length ≤ (journal k cs).length →
      ∀ i, 0 < i → i < t.length →
        tagged (some k) ((journal k cs).length + i) (t.drop i) = false := by
    intro cs t hct hle i hi _
    have := hno ((journal k cs).length + i) (by omega)
    rwa [hct, drop_after] at this
  cases hg0 : g.isEmpty with
  | true =>
    have hg' : g = [] := List.isEmpty_iff.mp hg0
    subst hg'
    refine ⟨rs, [], by simp, Or.inl rfl, ?_⟩
    simp [scan_encoded k hk rs hrs]
  | false =>
    cases htg : tagged (some k) (journal k rs).length g with
    | false =>
      refine ⟨rs, g, rfl, Or.inl rfl, ?_⟩
      have hl : (journal k rs ++ g).length ≤ (journal k rs).length + maxFrame :=
        Nat.le_trans hlen hhigh
      rw [List.length_append] at hl
      refine scan_rest k hk rs hrs g (by omega) fun i hi => ?_
      cases i with
      | zero => simpa using htg
      | succ i => exact hafter rs g rfl (Nat.le_refl _) (i + 1) (by omega) hi
    | true =>
      have htg' : tagged (some k) (journal k rs).length
          ((journal k rs ++ g).drop (journal k rs).length) = true := by
        rw [List.drop_left]; exact htg
      obtain ⟨w, hw, hf⟩ := hu _ (by rw [hkept]; exact Nat.le_refl _) htg'
      rw [List.drop_left] at hf
      obtain ⟨r, hr, hkey, hwr'⟩ := (hwr _ w hw).2 (by omega)
      obtain ⟨⟨t, rfl⟩, h2⟩ := frame_encode g w r hr k _ (tagged_whole _ _ _ htg) hf hwr'
      have hj : journal k rs ++ (r.encode k (journal k rs).length ++ t) = journal k (rs ++ [r]) ++ t
          := by rw [journal_append, List.append_assoc]
      have hl : (journal k rs ++ (r.encode k (journal k rs).length ++ t)).length ≤ d.high := hlen
      simp only [List.length_append] at hl
      have hP := hback w r hw hr h2 (by omega)
      refine ⟨rs ++ [r], t, hj, Or.inr ⟨r, hP, hr, hkey, rfl⟩, ?_⟩
      rw [hj]
      have hjl : (journal k (rs ++ [r])).length =
          (journal k rs).length + (r.encode k (journal k rs).length).length := by
        rw [journal_append, List.length_append]
      refine scan_rest k hk _ (appends_snoc rs hrs r hr hkey) t (by omega) fun i hi => ?_
      have he := encode_length r k (journal k rs).length
      have := hno ((journal k (rs ++ [r])).length + i) (by rw [hjl]; omega)
      rwa [hj, drop_after] at this

/-- **A crash of the journal while its format is written reads, without corruption, as nothing,
as a torn tail at its start, or as the format of a journal with no record**, one a creation
wrote. -/
theorem creating_crash (d : Data) (h : Creating d) (c : Bytes) (hc : d.Leaves c)
    (hu : FormatWritten d c) :
    (c = [] ∧ scan c = ⟨[], .clean⟩) ∨ (c ≠ [] ∧ c.length ≤ firstFrame ∧ scan c = ⟨[], .torn 0⟩) ∨
      ∃ k' w, k'.length = keyLength ∧ c = journal k' [] ∧ scan c = ⟨[.format k'], .clean⟩ ∧
        (0, w) ∈ d.written ∧ journal k' [] <+: w := by
  obtain ⟨hkept, hhigh, hwr⟩ := h
  obtain ⟨_, hlen⟩ := hc
  cases hc0 : c.isEmpty with
  | true =>
    have hc' : c = [] := List.isEmpty_iff.mp hc0
    subst hc'
    exact Or.inl ⟨rfl, by simp [scan, scanWith, scanFrom, next]⟩
  | false =>
    have hne : c ≠ [] := fun he => by simp [he] at hc0
    cases htg : tagged none 0 c with
    | false =>
      rcases tagged_false _ _ _ htg with hn | ⟨w, hn, hw⟩
      · exact absurd (next_done _ _ _ _ hn) hne
      · exact Or.inr (Or.inl ⟨hne, by omega, scan_stop_first c w hn hw (by omega)⟩)
    | true =>
      obtain ⟨w, hw, hf⟩ := hu htg
      obtain ⟨_, k', hk', hwk⟩ := hwr 0 w hw
      obtain ⟨h1, h2⟩ := frame_encode c w (.format k') (by simp [Record.ok, hk']) k' 0
        (tagged_whole _ _ _ htg) hf hwk
      have hj : journal k' [] = (Record.format k').encode k' 0 := by simp [journal, encodeFrom]
      have hce : c = journal k' [] := by
        have hl := h1.length_le
        rw [format_encode_length k' hk'] at hl
        rw [hj]
        exact (h1.eq_of_length (by rw [format_encode_length k' hk']; omega)).symm
      refine Or.inr (Or.inr ⟨k', w, hk', hce, ?_, hw, hj ▸ h2⟩)
      rw [hce]
      exact scan_encoded k' hk' [] (by simp [Appends])

/-! ## What the store does to the journal -/

theorem written_sync (d : Data) : d.sync.written = d.written := by
  unfold Data.sync; split <;> rfl

theorem seen_sync (d : Data) : d.sync.seen = d.seen := by
  unfold Data.sync; split <;> rfl

theorem high_sync (d : Data) (ht : d.trusted = true) : d.sync.high = d.seen.length := by
  simp [Data.sync, ht]

/-- **A restart is a crash that loses nothing**: the next start's first sync of the journal, while
syncs are trusted, leaves it as a crash that kept what the program saw. -/
theorem sync_after (d : Data) (ht : d.trusted = true) : d.sync = d.after d.seen := by
  simp [Data.sync, Data.after, ht]

/-- A file just created is a journal whose format is being written. -/
theorem creating_empty : Creating Data.empty :=
  ⟨rfl, Nat.zero_le _, fun _ _ h => by simp [Data.empty] at h⟩

/-- The format appended, whole or in part, to a journal that holds nothing. -/
theorem creating_append (d : Data) (h : Creating d) (hs : d.seen = []) (k : Bytes)
    (hk : k.length = keyLength) (j : Nat) :
    Creating (d.append (((Record.format k).encode k 0).take j)) := by
  obtain ⟨hkept, hhigh, hwr⟩ := h
  have hf := format_encode_length k hk 0
  refine ⟨hkept, ?_, fun o w hw => ?_⟩
  · simp only [Data.append, hs, List.length_nil, Nat.zero_add, List.length_take, hf]; omega
  · simp only [Data.append, hs, List.length_nil, List.mem_append, List.mem_singleton,
      Prod.mk.injEq] at hw
    rcases hw with hw | ⟨rfl, rfl⟩
    · exact hwr o w hw
    · exact ⟨rfl, k, hk, List.take_prefix _ _⟩

theorem creating_untrust (d : Data) (h : Creating d) : Creating d.untrust :=
  ⟨h.kept, h.high, h.written⟩

/-- The journal of no record, kept, with no append made where it ends. -/
theorem steady_format (d : Data) (h : Creating d) (k : Bytes) (hk : k.length = keyLength)
    (d' : Data) (hkept : d'.kept = journal k []) (hhigh : d'.high = (journal k []).length)
    (hw : d'.written = d.written) : Steady k [] (fun _ => False) d' ∧ Fresh k [] d' := by
  have hx := journal_length k hk []
  have hff : 0 < firstFrame := by decide
  have hzero : ∀ o w, (o, w) ∈ d'.written → o = 0 := fun o w hm => (h.written o w (hw ▸ hm)).1
  refine ⟨⟨hk, by simp [Appends], hkept, by omega, fun o w hm => ?_, fun w r hm _ _ _ => ?_⟩,
    fun o w hm => ?_⟩
  · have := hzero o w hm
    exact ⟨by omega, fun ho => absurd this (by omega)⟩
  · have := hzero _ w hm
    omega
  · have := hzero o w hm
    omega

/-- **The format synced**: the journal of no record, kept. -/
theorem creating_sync (d : Data) (h : Creating d) (ht : d.trusted = true) (k : Bytes)
    (hk : k.length = keyLength) (hs : d.seen = journal k []) :
    Steady k [] (fun _ => False) d.sync ∧ Fresh k [] d.sync :=
  steady_format d h k hk d.sync (by simp [Data.sync, ht, hs]) (by simp [Data.sync, ht, hs])
    (written_sync d)

/-- What a crash left of a journal whose format was being written, when it reads as a format: the
journal of no record, kept. -/
theorem creating_formatted (d : Data) (h : Creating d) (k : Bytes) (hk : k.length = keyLength) :
    Steady k [] (fun _ => False) (d.after (journal k [])) ∧ Fresh k [] (d.after (journal k [])) :=
  steady_format d h k hk _ rfl rfl rfl

/-- **A record appended** where the records kept end, whole or in part — where nothing was
appended before, or a start: a crash may leave whole there only that record. -/
theorem steady_append (k : Bytes) (rs : List Record) (P : Record → Prop) (d : Data)
    (h : Steady k rs P d) (hs : d.seen = journal k rs) (hh : d.high = (journal k rs).length)
    (r : Record) (hr : r.ok = true) (hkey : r.key = none) (hf : Fresh k rs d ∨ r = .start)
    (j : Nat) :
    Steady k rs (· = r) (d.append ((r.encode k (journal k rs).length).take j)) := by
  obtain ⟨hk, hrs, hkept, hhigh, hwr, hback⟩ := h
  have hx := journal_length k hk rs
  have hff : 0 < firstFrame := by decide
  have hle := encode_le r hr k (journal k rs).length
  have hnew : (d.append ((r.encode k (journal k rs).length).take j)).high =
      (journal k rs).length + min j (r.encode k (journal k rs).length).length := by
    simp only [Data.append, hs, hh, List.length_take]; omega
  refine ⟨hk, hrs, hkept, by rw [hnew]; omega, fun o w hm => ?_, fun w q hm hq hqw hfit => ?_⟩
  · simp only [Data.append, hs, List.mem_append, List.mem_singleton, Prod.mk.injEq] at hm
    rcases hm with hm | ⟨rfl, rfl⟩
    · exact hwr o w hm
    · exact ⟨Nat.le_refl _, fun _ => ⟨r, hr, hkey, List.take_prefix _ _⟩⟩
  · rw [hnew] at hfit
    simp only [Data.append, hs, List.mem_append, List.mem_singleton, Prod.mk.injEq] at hm
    rcases hm with hm | ⟨_, rfl⟩
    · rcases hf with hf | rfl
      · have := hf _ w hm
        omega
      · refine Classical.byContradiction fun hne => ?_
        have := start_shortest q hne k k (journal k rs).length (journal k rs).length
        omega
    · exact encode_prefix r q hr hq k _ (hqw.trans (List.take_prefix _ _))

/-- **The record appended, synced**: the journal of one more record, kept, with nothing appended
where it now ends. -/
theorem steady_sync (k : Bytes) (rs : List Record) (P : Record → Prop) (d : Data)
    (h : Steady k rs P d) (ht : d.trusted = true) (r : Record) (hr : r.ok = true)
    (hkey : r.key = none) (hs : d.seen = journal k rs ++ r.encode k (journal k rs).length) :
    Steady k (rs ++ [r]) (fun _ => False) d.sync ∧ Fresh k (rs ++ [r]) d.sync := by
  obtain ⟨hk, hrs, _, _, hwr, _⟩ := h
  have hj := journal_append k rs r
  have hlen : (journal k (rs ++ [r])).length =
      (journal k rs).length + (r.encode k (journal k rs).length).length := by
    rw [hj, List.length_append]
  have he := encode_length r k (journal k rs).length
  rw [← hj] at hs
  have hws := written_sync d
  refine ⟨⟨hk, appends_snoc rs hrs r hr hkey, by simp [Data.sync, ht, hs],
    by simp [Data.sync, ht, hs], fun o w hm => ?_, fun w q hm _ _ _ => ?_⟩, fun o w hm => ?_⟩
  · rw [hws] at hm
    obtain ⟨h1, h2⟩ := hwr o w hm
    exact ⟨by omega, h2⟩
  · rw [hws] at hm
    have := (hwr _ w hm).1
    omega
  · rw [hws] at hm
    have := (hwr o w hm).1
    omega

/-- **The records kept, synced**: a crash leaves nothing after them. -/
theorem steady_sync_same (k : Bytes) (rs : List Record) (P : Record → Prop) (d : Data)
    (h : Steady k rs P d) (ht : d.trusted = true) (hs : d.seen = journal k rs) :
    Steady k rs (fun _ => False) d.sync := by
  obtain ⟨hk, hrs, _, _, hwr, _⟩ := h
  refine ⟨hk, hrs, by simp [Data.sync, ht, hs], by simp [Data.sync, ht, hs],
    fun o w hm => hwr o w (written_sync d ▸ hm), fun w q _ _ _ hfit => ?_⟩
  simp only [Data.sync, ht, hs, ↓reduceIte] at hfit
  have := encode_length q k (journal k rs).length
  omega

/-- `Steady` asks only what the file kept, the most it held and what was appended to it. -/
theorem steady_congr (k : Bytes) (rs : List Record) (P : Record → Prop) (d d' : Data)
    (h : Steady k rs P d) (hk : d'.kept = d.kept) (hh : d'.high = d.high)
    (hw : d'.written = d.written) : Steady k rs P d' :=
  ⟨h.key, h.records, hk ▸ h.kept, hh ▸ h.high, hw ▸ h.written, hw ▸ hh ▸ h.back⟩

theorem steady_untrust (k : Bytes) (rs : List Record) (P : Record → Prop) (d : Data)
    (h : Steady k rs P d) : Steady k rs P d.untrust :=
  steady_congr k rs P d _ h rfl rfl rfl

/-- **What a crash left, cut where the records it reads end**, is the journal of those records
kept; a record written whole where they end, that a crash may still leave there, is one allowed
before. -/
theorem steady_cut (k : Bytes) (rs : List Record) (P : Record → Prop) (d : Data)
    (h : Steady k rs P d) (c : Bytes) (hc : d.Leaves c) (rs' : List Record) (t : Bytes)
    (hct : c = journal k rs' ++ t)
    (hrs : rs' = rs ∨ ∃ r, r.ok = true ∧ r.key = none ∧ rs' = rs ++ [r]) :
    Steady k rs' P ((d.after c).truncate (journal k rs').length) ∧
      ((d.after c).truncate (journal k rs').length).seen = journal k rs' := by
  obtain ⟨hk, hrs0, hkept, hhigh, hwr, hback⟩ := h
  have hcl := hc.2
  have hy : (journal k rs).length ≤ (journal k rs').length := by
    rcases hrs with rfl | ⟨r, _, _, rfl⟩
    · exact Nat.le_refl _
    · rw [journal_append, List.length_append]; omega
  have htake : c.take (journal k rs').length = journal k rs' := by
    rw [hct]; exact List.take_left' rfl
  have hcy : (journal k rs').length ≤ c.length := by rw [hct, List.length_append]; omega
  have hd : (d.after c).truncate (journal k rs').length =
      ⟨journal k rs', journal k rs', c.length, d.written, true⟩ := by
    simp only [Data.truncate, Data.after, htake]
    rw [Nat.sub_eq_zero_of_le hcy, List.replicate_zero, List.append_nil,
      Nat.max_eq_left hcy]
  rw [hd]
  refine ⟨⟨hk, ?_, rfl, by simp only; omega, fun o w hm => ?_, fun w q hm hq hqw hfit => ?_⟩, rfl⟩
  · rcases hrs with rfl | ⟨r, hr, hkey, rfl⟩
    · exact hrs0
    · exact appends_snoc rs hrs0 r hr hkey
  · obtain ⟨h1, h2⟩ := hwr o w hm
    exact ⟨by omega, h2⟩
  · rcases hrs with rfl | ⟨r, _, _, rfl⟩
    · exact hback w q hm hq hqw (by simp only at hfit; omega)
    · have := (hwr _ w hm).1
      rw [journal_append, List.length_append] at this
      have := encode_length r k (journal k rs).length
      omega

/-! ## What a crash left -/

/-- A file all of whose octets are kept is left as it is by a sync. -/
theorem sync_settled (d : Data) (hk : d.kept = d.seen) (hh : d.high = d.seen.length) :
    d.sync = d := by
  unfold Data.sync
  split
  · cases d; simp_all
  · rfl

/-- **What a crash left of a journal whose format was being written**, when it reads as no format:
all of it kept, no longer than the format's frame, reading as nothing or as a torn tail at its
start, and appends only of formats, at its start. -/
structure Unformatted (d : Data) : Prop where
  kept : d.kept = d.seen
  high : d.high = d.seen.length
  short : d.seen.length ≤ firstFrame
  reads : scan d.seen = ⟨[], if d.seen.isEmpty then .clean else .torn 0⟩
  written : ∀ o w, (o, w) ∈ d.written →
    o = 0 ∧ ∃ k, k.length = keyLength ∧ w <+: (Record.format k).encode k 0

/-- **What a crash left of a journal whose format is kept**, before any cut: all of it kept,
reading as the format under `k`, the records `rs` and a torn tail or nothing; cut where the records
end, it is the journal of `rs` kept, and a crash may then leave whole there only a record `P`
allows. -/
structure Found (k : Bytes) (rs : List Record) (P : Record → Prop) (d : Data) : Prop where
  kept : d.kept = d.seen
  high : d.high = d.seen.length
  reads : ∃ t, d.seen = journal k rs ++ t ∧
    scan d.seen = ⟨.format k :: rs, if t.isEmpty then .clean else .torn (journal k rs).length⟩
  cut : Steady k rs P (d.truncate (journal k rs).length)

/-- Once a file holds no more than the records kept, a crash can leave nothing whole after them. -/
theorem steady_none (k : Bytes) (rs : List Record) (P : Record → Prop) (d : Data)
    (h : Steady k rs P d) (hh : d.high = (journal k rs).length) :
    Steady k rs (fun _ => False) d := by
  refine ⟨h.key, h.records, h.kept, h.high, h.written, fun w q _ _ _ hfit => ?_⟩
  have := encode_length q k (journal k rs).length
  omega

/-- The journal of its records kept, all of it, is also what a crash left of it. -/
theorem steady_settled_found (k : Bytes) (rs : List Record) (P : Record → Prop) (d : Data)
    (h : Steady k rs P d) (hk : d.kept = d.seen) (hh : d.high = d.seen.length) :
    Found k rs P d := by
  have hs : d.seen = journal k rs := hk ▸ h.kept
  refine ⟨hk, hh, ⟨[], by simp [hs], ?_⟩, steady_congr k rs P _ _ h ?_ ?_ rfl⟩
  · simp [hs, scan_encoded k h.key rs h.records]
  · simp [Data.truncate, hk, hs]
  · simp only [Data.truncate, hh, hs]; omega

/-- **A crash of the journal while its format is written** leaves it unformatted, or the journal
of no record. -/
theorem crash_unformatted (d : Data) (h : Creating d) (c : Bytes) (hc : d.Leaves c)
    (hu : FormatWritten d c) :
    Unformatted (d.after c) ∨ ∃ k, k.length = keyLength ∧ c = journal k [] ∧
      Found k [] (fun _ => False) (d.after c) := by
  rcases creating_crash d h c hc hu with ⟨rfl, hs⟩ | ⟨hne, hl, hs⟩ | ⟨k, _, hk, rfl, _⟩
  · exact Or.inl ⟨rfl, rfl, Nat.zero_le _, by simpa using hs, h.written⟩
  · have he : c.isEmpty = false := by cases c <;> simp_all
    exact Or.inl ⟨rfl, rfl, hl, by simp only [Data.after, he]; exact hs, h.written⟩
  · exact Or.inr ⟨k, hk, rfl,
      steady_settled_found k [] _ _ (creating_formatted d h k hk).1 rfl rfl⟩

/-- A crash of what a crash left changes nothing. -/
theorem unformatted_crash (d : Data) (h : Unformatted d) (c : Bytes) (hc : d.Leaves c) :
    c = d.seen ∧ Unformatted (d.after c) := by
  have he := (leaves_exact d h.kept h.high c).mp hc
  subst he
  exact ⟨rfl, ⟨rfl, rfl, h.short, h.reads, h.written⟩⟩

theorem unformatted_sync (d : Data) (h : Unformatted d) : Unformatted d.sync := by
  rw [sync_settled d h.kept h.high]; exact h

theorem unformatted_untrust (d : Data) (h : Unformatted d) : Unformatted d.untrust :=
  ⟨h.kept, h.high, h.short, h.reads, h.written⟩

/-- **Made again**: what a crash left with no format, cut to nothing, is a journal whose format is
being written. -/
theorem unformatted_again (d : Data) (h : Unformatted d) :
    Creating (d.truncate 0) ∧ (d.truncate 0).seen = [] := by
  refine ⟨⟨by simp [Data.truncate], ?_, fun o w hw => h.written o w hw⟩, by simp [Data.truncate]⟩
  have := h.short
  simp only [Data.truncate, h.high]
  omega

/-- **A restart while the format is written**, syncs trusted, is a crash that kept what the program
saw: what it saw, it appended, so nothing is assumed. -/
theorem restart_unformatted (d : Data) (h : Creating d) (hok : d.Ok) (ht : d.trusted = true)
    (hs : d.seen = [] ∨ (0, d.seen) ∈ d.written) :
    Unformatted d.sync ∨ ∃ k, k.length = keyLength ∧ d.seen = journal k [] ∧
      Found k [] (fun _ => False) d.sync := by
  rw [sync_after d ht]
  refine crash_unformatted d h d.seen (leaves_seen d hok) ?_
  rcases hs with hs | hs
  · rw [hs]; exact formatWritten_nil d
  · exact fun _ => ⟨d.seen, hs, List.take_prefix _ _⟩

/-- **A crash of the journal once its format is kept** leaves what reads as the records kept and
perhaps one more, a record `P` allows. -/
theorem crash_found (k : Bytes) (rs : List Record) (P : Record → Prop) (d : Data)
    (h : Steady k rs P d) (c : Bytes) (hc : d.Leaves c) (hu : Unforged k d c) :
    ∃ rs', (rs' = rs ∨ ∃ r, P r ∧ r.ok = true ∧ r.key = none ∧ rs' = rs ++ [r]) ∧
      Found k rs' P (d.after c) := by
  obtain ⟨rs', t, hct, hrs, hs⟩ := steady_crash k rs P d h c hc hu
  have hrs' : rs' = rs ∨ ∃ r, r.ok = true ∧ r.key = none ∧ rs' = rs ++ [r] := by
    rcases hrs with h1 | ⟨r, _, hr, hk, h2⟩
    · exact Or.inl h1
    · exact Or.inr ⟨r, hr, hk, h2⟩
  exact ⟨rs', hrs, rfl, rfl, ⟨t, hct, hs⟩, (steady_cut k rs P d h c hc rs' t hct hrs').1⟩

/-- A crash of what a crash left changes nothing. -/
theorem found_crash (k : Bytes) (rs : List Record) (P : Record → Prop) (d : Data)
    (h : Found k rs P d) (c : Bytes) (hc : d.Leaves c) : c = d.seen ∧ Found k rs P (d.after c) := by
  have he := (leaves_exact d h.kept h.high c).mp hc
  subst he
  refine ⟨rfl, rfl, rfl, h.reads, steady_congr k rs P _ _ h.cut ?_ ?_ rfl⟩
  · simp [Data.truncate, Data.after, h.kept]
  · simp [Data.truncate, Data.after, h.high]

theorem found_sync (k : Bytes) (rs : List Record) (P : Record → Prop) (d : Data)
    (h : Found k rs P d) : Found k rs P d.sync := by
  rw [sync_settled d h.kept h.high]; exact h

theorem found_untrust (k : Bytes) (rs : List Record) (P : Record → Prop) (d : Data)
    (h : Found k rs P d) : Found k rs P d.untrust :=
  ⟨h.kept, h.high, h.reads, steady_congr k rs P _ _ h.cut rfl rfl rfl⟩

/-- **Cut where its records end**, what a crash left is the journal of those records kept. -/
theorem found_cut (k : Bytes) (rs : List Record) (P : Record → Prop) (d : Data)
    (h : Found k rs P d) :
    Steady k rs P (d.truncate (journal k rs).length) ∧
      (d.truncate (journal k rs).length).seen = journal k rs := by
  refine ⟨h.cut, ?_⟩
  obtain ⟨t, ht, _⟩ := h.reads
  have hl : (journal k rs).length ≤ d.seen.length := by rw [ht, List.length_append]; omega
  simp only [Data.truncate, ht]
  rw [Nat.sub_eq_zero_of_le (by rw [← ht]; exact hl), List.replicate_zero, List.append_nil]
  exact List.take_left' rfl

/-- What a crash left that reads cleanly needs no cut: it is the journal of its records kept, after
which a crash can leave nothing whole. -/
theorem found_clean (k : Bytes) (rs : List Record) (P : Record → Prop) (d : Data)
    (h : Found k rs P d) (hs : d.seen = journal k rs) : Steady k rs (fun _ => False) d := by
  refine steady_none k rs P d (steady_congr k rs P _ _ h.cut ?_ ?_ rfl) (by rw [h.high, hs])
  · simp [Data.truncate, h.kept, hs]
  · simp only [Data.truncate, h.high, hs]; omega

/-- **A restart once the format is kept**, syncs trusted, is a crash that kept what the program
saw. -/
theorem restart_found (k : Bytes) (rs : List Record) (P : Record → Prop) (d : Data)
    (h : Steady k rs P d) (hok : d.Ok) (ht : d.trusted = true) (hu : Unforged k d d.seen) :
    ∃ rs', (rs' = rs ∨ ∃ r, P r ∧ r.ok = true ∧ r.key = none ∧ rs' = rs ++ [r]) ∧
      Found k rs' P d.sync := by
  rw [sync_after d ht]
  exact crash_found k rs P d h d.seen (leaves_seen d hok) hu

/-! ## The premises can hold -/

theorem sampleKey_length : sampleKey.length = keyLength := by simp [sampleKey, keyLength]

/-- The premises `Steady` and `Fresh` can hold: of the journal of no record. -/
theorem steady_witness :
    Steady sampleKey [] (fun _ => False) (Data.empty.after (journal sampleKey [])) ∧
      Fresh sampleKey [] (Data.empty.after (journal sampleKey [])) :=
  creating_formatted Data.empty creating_empty sampleKey sampleKey_length

/-- Three octets of a start, its length's zeros, appended to the journal of no record. -/
def sampleAppended : Data :=
  (Data.empty.after (journal sampleKey [])).append
    ((Record.start.encode sampleKey (journal sampleKey []).length).take 3)

/-- What a crash may leave of it: all of it. -/
def sampleLeft : Bytes :=
  journal sampleKey [] ++ (Record.start.encode sampleKey (journal sampleKey []).length).take 3

/-- The premises of `steady_crash` can hold together, of a crash that leaves octets past those
kept: `Steady`, `Data.Leaves` and `Unforged`. -/
theorem crash_witness :
    Steady sampleKey [] (· = .start) sampleAppended ∧ sampleAppended.Leaves sampleLeft ∧
      Unforged sampleKey sampleAppended sampleLeft := by
  have he := encode_length Record.start sampleKey (journal sampleKey []).length
  refine ⟨steady_append sampleKey [] _ _ steady_witness.1 rfl rfl .start rfl rfl (Or.inr rfl) 3,
    ⟨List.prefix_append _ _, ?_⟩, fun o ho ht => ?_⟩
  · simp only [sampleAppended, sampleLeft, Data.append, Data.after, List.length_append,
      List.length_take]
    omega
  · have hw := tagged_whole _ _ _ ht
    have hl : (sampleLeft.drop o).length ≤ 3 := by
      simp only [sampleAppended, Data.append, Data.after] at ho
      simp only [sampleLeft, List.length_drop, List.length_append, List.length_take]
      omega
    simp only [headerLength] at hw
    omega

/-- The premise `Found` can hold: of that crash. -/
theorem found_witness : ∃ rs P, Found sampleKey rs P (sampleAppended.after sampleLeft) := by
  obtain ⟨hs, hc, hu⟩ := crash_witness
  obtain ⟨rs, _, hf⟩ := crash_found _ _ _ _ hs _ hc hu
  exact ⟨rs, _, hf⟩

/-- The premise `FormatWritten` can hold: of a format appended, left whole. -/
theorem formatWritten_witness :
    FormatWritten (Data.empty.append (journal sampleKey [])) (journal sampleKey []) :=
  fun _ => ⟨journal sampleKey [], by simp [Data.append, Data.empty], List.take_prefix _ _⟩

/-- The premise `Unformatted` can hold: of a format whose append a crash cut after three octets. -/
theorem unformatted_witness :
    Unformatted ((Data.empty.append (journal sampleKey [])).after
      ((journal sampleKey []).take 3)) := by
  have hj : journal sampleKey [] = (Record.format sampleKey).encode sampleKey 0 := by
    simp [journal, encodeFrom]
  have hl := format_encode_length sampleKey sampleKey_length 0
  have hff : 3 < firstFrame := by simp only [firstFrame, headerLength]; omega
  have h3 : ((journal sampleKey []).take 3).length = 3 := by
    rw [List.length_take, hj, hl]; omega
  have hn := next_short (.format sampleKey) (by simp [Record.ok, sampleKey_length]) sampleKey 0
    none 0 3 (by decide) (by rw [hl]; exact hff)
  have he : ((journal sampleKey []).take 3).isEmpty = false := by
    cases h : (journal sampleKey []).take 3 with
    | nil => rw [h] at h3; cases h3
    | cons _ _ => rfl
  refine ⟨rfl, rfl, by simp only [Data.after, h3]; omega, ?_, fun o w hw => ?_⟩
  · simp only [Data.after, he, Bool.false_eq_true, ↓reduceIte]
    rw [hj] at h3 ⊢
    exact scan_stop_first _ .short hn rfl (by omega)
  · simp only [Data.after, Data.append, Data.empty, List.nil_append, List.mem_singleton,
      Prod.mk.injEq, List.length_nil] at hw
    obtain ⟨rfl, rfl⟩ := hw
    exact ⟨rfl, sampleKey, sampleKey_length, hj ▸ List.prefix_refl _⟩

/-! ## Examples -/

def commitOf (seq : Nat) : Commit := ⟨seq, ascii "<x@y>", [⟨ascii "local.test", seq⟩], 1, 1, 0⟩

/-- The journal's file as the store makes it: its format appended and synced, then each record
appended at its end and synced. -/
def built (k : Bytes) (rs : List Record) : Data :=
  rs.foldl (fun d r => (d.append (r.encode k d.seen.length)).sync)
    (Data.empty.append (journal k [])).sync

/-- How the crashes `cuts` lists read back. -/
def readings (d : Data) : List Scan :=
  ((d.cuts.filter d.leaves).map scan).eraseDups

def sound (s : Scan) : Bool :=
  match s.ending with
  | .corrupt .. => false
  | _ => true

/-- A commit appended and not synced: a crash leaves the records kept, the commit whole, or a torn
tail, never corruption, and the assumption holds of every crash listed; one that changes an octet of
the commit leaves a torn tail; a commit framed where it lies but never appended is what the
assumption rules out. -/
def regression_912 : Bool :=
  let k := sampleKey
  let rs := [Record.start, .commit (commitOf 1)]
  let x := (journal k rs).length
  let c2 := (Record.commit (commitOf 2)).encode k x
  let d := (built k rs).append c2
  let rd := readings d
  let junk := journal k rs ++ c2.set 13 7
  let forged := journal k rs ++ (Record.commit (commitOf 3)).encode k x
  d.cuts.all (unforged k d) &&
    d.leaves junk && unforged k d junk && scan junk == ⟨.format k :: rs, .torn x⟩ &&
    d.leaves forged && !unforged k d forged &&
    scan forged == ⟨.format k :: rs ++ [.commit (commitOf 3)], .clean⟩ &&
    rd.all (fun s => s == ⟨.format k :: rs, .clean⟩ || s == ⟨.format k :: rs, .torn x⟩ ||
      s == ⟨.format k :: rs ++ [.commit (commitOf 2)], .clean⟩) &&
    rd.contains ⟨.format k :: rs, .torn x⟩ &&
    rd.contains ⟨.format k :: rs ++ [.commit (commitOf 2)], .clean⟩

/-- A commit whose end mark a crash lost, cut away and the cut not synced: a crash may bring it back
whole, and still after a start appended to that cut; once the cut is synced it never comes back,
nor after a start appended where it was — but it may after a commit as long, which is why the cut
is synced first and a run's first append is its start. -/
def regression_913 : Bool :=
  let k := sampleKey
  let rs := [Record.start, .commit (commitOf 1)]
  let x := (journal k rs).length
  let c2 := (Record.commit (commitOf 2)).encode k x
  let d := (built k rs).append c2
  let left := journal k rs ++ c2.dropLast ++ [0]
  let cut := (d.after left).truncate x
  let synced := cut.sync
  let started := synced.append (Record.start.encode k x)
  let early := cut.append (Record.start.encode k x)
  let other := synced.append ((Record.commit (commitOf 3)).encode k x)
  let back := journal k rs ++ c2
  d.leaves left && scan left == ⟨.format k :: rs, .torn x⟩ &&
    cut.cuts.all (unforged k cut) && synced.cuts.all (unforged k synced) &&
    started.cuts.all (unforged k started) &&
    let rc := readings cut
    rc.all (fun s => sound s && (s.records == .format k :: rs ||
      s.records == .format k :: rs ++ [.commit (commitOf 2)])) &&
    rc.contains ⟨.format k :: rs ++ [.commit (commitOf 2)], .clean⟩ &&
    readings synced == [⟨.format k :: rs, .clean⟩] &&
    (readings started).all (fun s => sound s &&
      (s.records == .format k :: rs || s.records == .format k :: rs ++ [.start])) &&
    scan back == ⟨.format k :: rs ++ [.commit (commitOf 2)], .clean⟩ &&
    early.leaves back && unforged k early back && !started.leaves back &&
    other.leaves back && unforged k other back

/-- A format being written: a crash leaves nothing, a torn tail at the start, or the format; made
again under another key after its end mark was lost, a crash may leave the format of either key,
and the format of a key no creation wrote is what the assumption rules out. -/
def regression_914 : Bool :=
  let k := sampleKey
  let k2 := sampleKey.map (· + 1)
  let f := journal k []
  let d := Data.empty.append f
  let rd := readings d
  let left := f.dropLast ++ [0]
  let again := ((d.after left).truncate 0).append (journal k2 [])
  let rd2 := readings again
  let other := journal (sampleKey.map (· + 2)) []
  d.cuts.all (formatWritten d) && again.cuts.all (formatWritten again) &&
  rd.contains ⟨[], .clean⟩ && rd.contains ⟨[], .torn 0⟩ && rd.contains ⟨[.format k], .clean⟩ &&
    rd.all (fun s => sound s && s.records.length ≤ 1) &&
    again.leaves f && formatWritten again f && scan f == ⟨[.format k], .clean⟩ &&
    again.leaves other && !formatWritten again other &&
    rd2.contains ⟨[.format k2], .clean⟩ && rd2.all (fun s => sound s && s.records.length ≤ 1)

end DN.News.JournalCrash
