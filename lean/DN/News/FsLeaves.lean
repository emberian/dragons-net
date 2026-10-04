-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.FsModel

/-!
# DN.News.FsLeaves

Whether a crash may leave the directory holding what an image says, decided (`mayLeave`): for each
name, what it held at the directory's last sync or anything it has held since, and for each file
octets its rule allows, one file under two names holding the same octets. It decides `Crash`:
of a well-formed file system, `mayLeave s img` holds exactly when some crash of `s` leaves `img`
(`mayLeave_iff`), so a check of it against an independent reading of decision 0005 checks the crash
model itself, as far as a crash shows in the directory it leaves.
-/

namespace DN.News.FsLeaves

open DN.News.FsModel

/-- What the program finds in the directory: each name that holds a file, with its octets. -/
abbrev Image := List (Bytes × Bytes)

/-- The names a crash leaving the names as `ns` says hold a file the file system has: each name,
its file and the file's data, in the directory's order. -/
def slots (s : Fs) (ns : List (Option Ino)) : List (Bytes × Ino × Data) :=
  (s.dir.zip ns).filterMap fun p => p.2.bind fun i => (s.data i).map fun d => (p.1.name, i, d)

/-- Whether a crash leaving the names as `ns` says may leave `img`: the same names in order, each
holding octets its file's rule allows, one file holding the same octets under every name. -/
def fits (s : Fs) (ns : List (Option Ino)) (img : Image) : Bool :=
  let sl := (slots s ns).zip img
  (slots s ns).length == img.length &&
    sl.all (fun q => q.1.1 == q.2.1 && q.1.2.2.leaves q.2.2) &&
    sl.all fun q => sl.all fun r => q.1.2.1 != r.1.2.1 || q.2.2 == r.2.2

/-- **Whether a crash may leave the directory holding `img`**: every file with octets its rule
allows, and the names as some choice for each lets `img` be. -/
def mayLeave (s : Fs) (img : Image) : Bool :=
  s.files.all (fun p => decide (p.2.kept.length ≤ p.2.high)) &&
    (product (s.dir.map fun e => e.synced :: e.held)).any fun ns => fits s ns img

/-! ## What a crash leaves, as an image -/

theorem filterMap_congr {α β : Type} {f g : α → Option β} :
    ∀ l : List α, (∀ x ∈ l, f x = g x) → l.filterMap f = l.filterMap g
  | [], _ => rfl
  | x :: l, h => by
    simp only [List.filterMap_cons, h x (List.mem_cons_self ..),
      filterMap_congr l fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem crashDir_eq :
    ∀ (es : List Entry) (bs : List (Option Ino)),
      crashDir es bs = (es.zip bs).filterMap fun p => p.2.map fun i => ⟨p.1.name, some i, []⟩
  | [], _ => by simp [crashDir]
  | _ :: _, [] => by simp [crashDir]
  | e :: es, b :: bs => by
    cases b <;> simp [crashDir, crashDir_eq es bs]

theorem find_zip {α β : Type} (P : α → Bool) :
    ∀ (as : List α) (bs : List β), as.length = bs.length →
      ((as.zip bs).find? (fun x => P x.1)).map Prod.fst = as.find? P
  | [], [], _ => rfl
  | a :: as, b :: bs, hl => by
    simp only [List.zip_cons_cons, List.find?_cons]
    cases P a
    · exact find_zip P as bs (by simpa using hl)
    · rfl
  | [], _ :: _, hl => by simp at hl
  | _ :: _, [], hl => by simp at hl

theorem mem_zip_map {α β : Type} (f : α → β) :
    ∀ (l : List α) (x : α × β), x ∈ l.zip (l.map f) → x.2 = f x.1
  | [], _, hx => by simp at hx
  | a :: l, x, hx => by
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · rfl
    · exact mem_zip_map f l x hx

/-- The octets `ds` gives the first file numbered `i`, none if there is none. -/
def val (s : Fs) (ds : List Bytes) (i : Ino) : Bytes :=
  (((s.files.zip ds).find? (i == ·.1.1)).map (·.2)).getD []

/-- The file numbered `i`, if the file system has one, with the octets `ds` gives it. -/
theorem val_of_data (s : Fs) (ds : List Bytes) (hl : s.files.length = ds.length) (i : Ino)
    (d : Data) (hd : s.data i = some d) :
    ∃ x ∈ s.files.zip ds, x.1.1 = i ∧ x.1.2 = d ∧ val s ds i = x.2 := by
  simp only [Fs.data, lookup_eq_find] at hd
  have hz := find_zip (fun x : Ino × Data => i == x.1) s.files ds hl
  cases hzf : (s.files.zip ds).find? (i == ·.1.1) with
  | none =>
    rw [hzf] at hz
    simp only [Option.map_none] at hz
    rw [← hz] at hd
    simp at hd
  | some x =>
    rw [hzf] at hz
    simp only [Option.map_some] at hz
    rw [← hz] at hd
    simp only [Option.map_some, Option.some.injEq] at hd
    have hxi := List.find?_some hzf
    simp only [beq_iff_eq] at hxi
    exact ⟨x, List.mem_of_find?_eq_some hzf, hxi.symm, hd, by simp [val, hzf]⟩

/-- **What a crash leaves, as the program reads it**: the names it leaves holding a file the file
system has, in order, each with the octets chosen for its file. -/
theorem image_crashWith (s : Fs) (ns : List (Option Ino)) (ds : List Bytes)
    (hl : s.files.length = ds.length) :
    (s.crashWith ⟨ns, ds⟩).image = (slots s ns).map fun q => (q.1, val s ds q.2.1) := by
  simp only [Fs.image, slots, List.map_filterMap, Fs.crashWith, Fs.prune, crashDir_eq,
    List.filterMap_filterMap]
  apply filterMap_congr
  intro p hp
  rcases p with ⟨e, _ | i⟩
  · rfl
  · have hholds : Fs.holds ⟨(s.dir.zip ns).filterMap fun p => p.2.map fun i =>
        (⟨p.1.name, some i, []⟩ : Entry), crashFiles s.files ds, s.next, true⟩ i = true := by
      simp only [Fs.holds, List.any_eq_true]
      refine ⟨⟨e.name, some i, []⟩, List.mem_filterMap.mpr ⟨(e, some i), hp, rfl⟩, ?_⟩
      simp [Entry.holds, Entry.Leaves]
    simp only [Option.map_some, Entry.seen, List.headD, Option.bind,
      Fs.data, lookup_filter, hholds, ↓reduceIte, lookup_crashFiles _ _ hl, Option.map_map]
    cases hd : s.files.lookup i with
    | none =>
      have hz := find_zip (fun x : Ino × Data => i == x.1) s.files ds hl
      rw [lookup_eq_find] at hd
      have : (s.files.find? (i == ·.1)) = none := by
        cases hf : s.files.find? (i == ·.1) with
        | none => rfl
        | some _ => rw [hf] at hd; simp at hd
      rw [this] at hz
      cases hzf : (s.files.zip ds).find? (i == ·.1.1) with
      | none => rfl
      | some _ => rw [hzf] at hz; simp at hz
    | some d =>
      have hd' : s.data i = some d := hd
      obtain ⟨x, _, _, _, hv⟩ := val_of_data s ds hl i d hd'
      have hz := find_zip (fun x : Ino × Data => i == x.1) s.files ds hl
      cases hzf : (s.files.zip ds).find? (i == ·.1.1) with
      | none =>
        rw [lookup_eq_find] at hd
        rw [hzf] at hz
        simp only [Option.map_none] at hz
        rw [← hz] at hd
        simp at hd
      | some y =>
        simp only [Option.map_some, Function.comp, Data.after, Option.some.injEq, Prod.mk.injEq,
          true_and]
        simp [val, hzf] at hv ⊢

/-! ## It decides `Crash` -/

theorem each_exists {α β : Type} (R : α → β → Prop) :
    ∀ (as : List α) (bs : List β), Each R as bs → ∀ a ∈ as, ∃ b, R a b
  | a :: as, b :: bs, ⟨h, hr⟩, x, hx => by
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨b, h⟩
    · exact each_exists R as bs hr x hx
  | [], _, _, _, hx => by simp at hx
  | _ :: _, [], h, _, _ => h.elim

theorem each_zip {α β : Type} (R : α → β → Prop) :
    ∀ (as : List α) (bs : List β), Each R as bs → ∀ x ∈ as.zip bs, R x.1 x.2
  | a :: as, b :: bs, ⟨h, hr⟩, x, hx => by
    simp only [List.zip_cons_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact h
    · exact each_zip R as bs hr x hx
  | [], _, _, _, hx => by simp at hx
  | _ :: _, [], _, _, hx => by simp at hx

theorem product_of_each {α : Type} :
    ∀ (xss : List (List α)) (l : List α), Each (fun xs x => x ∈ xs) xss l → l ∈ product xss
  | [], [], _ => by simp [product]
  | xs :: xss, x :: l, ⟨h, hr⟩ => by
    simp only [product, List.mem_flatMap, List.mem_map]
    exact ⟨x, h, l, product_of_each xss l hr, rfl⟩
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem each_map_of {α β γ : Type} (R : β → γ → Prop) (f : α → β) :
    ∀ (as : List α) (cs : List γ), Each (fun a c => R (f a) c) as cs → Each R (as.map f) cs
  | [], [], _ => trivial
  | _ :: as, _ :: cs, ⟨h, hr⟩ => ⟨h, each_map_of R f as cs hr⟩
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem map_eq_of_zip {α β : Type} (f : α → β) :
    ∀ (as : List α) (bs : List β), as.length = bs.length → (∀ x ∈ as.zip bs, f x.1 = x.2) →
      as.map f = bs
  | [], [], _, _ => rfl
  | a :: as, b :: bs, hl, h => by
    simp only [List.map_cons, List.cons.injEq]
    refine ⟨h (a, b) (by simp), map_eq_of_zip f as bs (by simpa using hl) fun x hx => ?_⟩
    exact h x (by simp [hx])
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

/-- A name's file in `slots` is one the file system has, with that data. -/
theorem slots_data (s : Fs) (ns : List (Option Ino)) (q : Bytes × Ino × Data)
    (hq : q ∈ slots s ns) : s.data q.2.1 = some q.2.2 := by
  simp only [slots, List.mem_filterMap] at hq
  obtain ⟨p, _, hp⟩ := hq
  rcases p with ⟨e, _ | i⟩
  · simp at hp
  · simp only [Option.bind_some] at hp
    cases hd : s.data i with
    | none => simp [hd] at hp
    | some d =>
      simp only [hd, Option.map_some, Option.some.injEq] at hp
      subst hp
      exact hd

/-- **Every image `mayLeave` admits is one a crash leaves.** -/
theorem mayLeave_sound (s : Fs) (hs : s.Ok) (img : Image) (h : mayLeave s img = true) :
    ∃ t, Crash s t ∧ t.image = img := by
  simp only [mayLeave, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    List.any_eq_true] at h
  obtain ⟨hall, ns, hns, hfit⟩ := h
  simp only [fits, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.or_eq_true,
    bne_iff_ne, ne_eq] at hfit
  obtain ⟨⟨hlen, hpair⟩, hsame⟩ := hfit
  let pick : Ino × Data → Bytes := fun p =>
    ((((slots s ns).zip img).find? (·.1.2.1 == p.1)).map (·.2.2)).getD p.2.kept
  let ds := s.files.map pick
  have hdl : s.files.length = ds.length := by simp [ds]
  -- the octets chosen for a slot's file are the image's
  have hpick : ∀ q ∈ (slots s ns).zip img, ∀ p : Ino × Data, p.1 = q.1.2.1 → pick p = q.2.2 := by
    intro q hq p hp
    simp only [pick]
    have hfind : (((slots s ns).zip img).find? (·.1.2.1 == p.1)).isSome := by
      rw [List.find?_isSome]
      exact ⟨q, hq, by simp [hp]⟩
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hfind
    have hrm := List.mem_of_find?_eq_some hr
    have hrp := List.find?_some hr
    simp only [beq_iff_eq] at hrp
    rw [hr]
    simp only [Option.map_some, Option.getD_some]
    rcases hsame r hrm q hq with hne | heq
    · exact absurd (hrp.trans hp) hne
    · exact heq
  have hkey : ∀ p ∈ s.files, s.data p.1 = some p.2 := fun p hp => by
    simp only [Fs.data, lookup_eq_find, find_key s.files hs.2.1 p hp, Option.map_some]
  refine ⟨s.crashWith ⟨ns, ds⟩, ⟨⟨ns, ds⟩, ⟨?_, ?_⟩, rfl⟩, ?_⟩
  · have := mem_product _ _ hns
    refine each_imp _ _ ?_ _ _ (each_map_left _ _ _ _ this)
    intro e b hb
    simpa [Entry.Leaves, List.mem_cons] using hb
  · refine each_map _ _ _ fun p hp => ?_
    simp only [pick]
    cases hf : ((slots s ns).zip img).find? (·.1.2.1 == p.1) with
    | none => exact ⟨List.prefix_refl _, hall p hp⟩
    | some q =>
      have hqm := List.mem_of_find?_eq_some hf
      have hqp := List.find?_some hf
      simp only [beq_iff_eq] at hqp
      have hd := slots_data s ns q.1 (List.of_mem_zip hqm).1
      rw [hqp, hkey p hp] at hd
      simp only [Option.map_some, Option.getD_some]
      have := (hpair q hqm).2
      rw [← Option.some.inj hd] at this
      exact (leaves_iff _ _).mp this
  · rw [image_crashWith s ns ds hdl]
    refine map_eq_of_zip _ _ _ hlen fun q hq => ?_
    obtain ⟨x, hxm, hxi, _, hv⟩ :=
      val_of_data s ds hdl q.1.2.1 q.1.2.2 (slots_data s ns q.1 (List.of_mem_zip hq).1)
    have hx2 : x.2 = pick x.1 := mem_zip_map pick s.files x hxm
    refine Prod.ext (hpair q hq).1 ?_
    show val s ds q.1.2.1 = q.2.2
    rw [hv, hx2, hpick q hq x.1 hxi]

/-- **Every image a crash leaves `mayLeave` admits.** -/
theorem mayLeave_complete (s t : Fs) (h : Crash s t) : mayLeave s t.image = true := by
  obtain ⟨⟨ns, ds⟩, ⟨hd, hf⟩, rfl⟩ := h
  have hdl : s.files.length = ds.length := each_length _ _ _ hf
  have hzip : ∀ x ∈ s.files.zip ds, Data.Leaves x.1.2 x.2 := each_zip _ _ _ hf
  rw [image_crashWith s ns ds hdl]
  let g : Bytes × Ino × Data → Bytes × Bytes := fun q => (q.1, val s ds q.2.1)
  have hg : ∀ y ∈ (slots s ns).zip ((slots s ns).map g), y.2 = g y.1 := mem_zip_map g _
  simp only [mayLeave, fits, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    List.any_eq_true, beq_iff_eq, List.length_map, Bool.or_eq_true, bne_iff_ne, ne_eq]
  refine ⟨fun p hp => ?_, ns,
    product_of_each _ _ (each_map_of _ _ _ _ (each_imp _ _ ?_ _ _ hd)), ⟨rfl, ?_⟩, ?_⟩
  · obtain ⟨c, hpre, hle⟩ := each_exists _ _ _ hf p hp
    exact Nat.le_trans hpre.length_le hle
  · intro e b hb
    simpa [Entry.Leaves, List.mem_cons] using hb
  · intro y hy
    rw [hg y hy]
    refine ⟨rfl, ?_⟩
    obtain ⟨x, hxm, _, hxd, hv⟩ :=
      val_of_data s ds hdl y.1.2.1 y.1.2.2 (slots_data s ns y.1 (List.of_mem_zip hy).1)
    show y.1.2.2.leaves (val s ds y.1.2.1) = true
    rw [hv, ← hxd, leaves_iff]
    exact hzip x hxm
  · intro y hy z hz
    rw [hg y hy, hg z hz]
    by_cases he : y.1.2.1 = z.1.2.1
    · exact Or.inr (by simp only [g, he])
    · exact Or.inl he

/-- **`mayLeave` decides what a crash may leave.** -/
theorem mayLeave_iff (s : Fs) (hs : s.Ok) (img : Image) :
    mayLeave s img = true ↔ ∃ t, Crash s t ∧ t.image = img :=
  ⟨mayLeave_sound s hs img, fun ⟨t, h, ht⟩ => ht ▸ mayLeave_complete s t h⟩

end DN.News.FsLeaves
