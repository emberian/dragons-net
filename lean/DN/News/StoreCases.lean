-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.StoreRun
import DN.News.FsCases

/-!
# DN.News.StoreCases

The store's program (`DN.News.StoreOps`, its start `DN.News.RecoveryRun`) run on cases, as
`dn-compiler store-model` answers them, a line each, for the lane that holds every point of its runs
to what a crash may leave there, after decision 0005 (`scripts/runs_check.py`):

    run KEY GROUPS RUN IMAGE EVENTS     a start on the directory IMAGE, then the events
    force KEY GROUPS RUN IMAGE EVENTS   the same, each event done whether the program may or not

KEY is the key of a journal the start would create and GROUPS the groups the store carries, as
`dn-compiler recovery-model` takes them; RUN is the run's number; IMAGE the directory as a crash
left it, every name and file synced, its files numbered in its order from 0. EVENTS is `-` or events
separated by `;`: `reserve:OCTETS`, `create:Q`, `write:Q:M`, `sync:Q`, `rename:Q`, `place:Q`,
`commit:Q:SEQ:MESSAGE-ID:GROUPS:HEADER:SIZE:CRC` (GROUPS `NAME=NUMBER,NAME=NUMBER`), `publish`,
`refuse:Q`, `clean:Q:0` (the temporary name) or `clean:Q:1` (the final one), `drop:Q`; one followed
by `!K` fails, its operation leaving the `K`-th outcome `Fs.failures` lists, as
`dn-compiler fs-model` numbers them. `restart` ends the process and starts the store again on the
file system as it is, under the next run's number; `restart:N:K` does, its start's `N`-th operation
failing with the `K`-th outcome, the process then down until a restart. The answer is
`corrupt WHY` if recovery refuses the directory, `not-allowed N` if the program may not make the
`N`-th event, `not-startable N` if `Reach` may not begin the `N`-th event's start, or
`ok OPERATIONS IMAGE`: the operations on the file system, in `dn-compiler fs-model`'s words, of the
start and of each event, those of one separated by `;` and each one's from the next by `|`, `-` for
none; then the directory the program then finds.
-/

namespace DN.News.StoreCases

open DN.News.Journal
open DN.News.FsModel (Data Entry Fs Ino Op)
open DN.News.Recovery
open DN.News.Spool (image startSyncs)
open DN.News.RecoveryRun (startOps)
open DN.News.StoreOps
open DN.News.StoreRun (startOn Hist.empty)
open DN.News.FrameModel (parseHex hex)
open DN.News.JournalModel (natOf)
open DN.News.RecoveryModel (joined items imageText faultText)
open DN.News.FsCases (parseOctets sortedImage)

/-! ## What a command does to the file system -/

/-- The operation a command makes on the file system, if it makes one. -/
def opOf (x : St) : Cmd → Option Op
  | .create q => (x.prog.posts q).map fun _ => .create (tempName q)
  | .write q m => match x.prog.posts q with
    | some y => match y.stage with
      | .writing i => some (.append i (y.chunk m))
      | _ => none
    | none => none
  | .sync q => match x.prog.posts q with
    | some y => match y.stage with
      | .writing i => some (.sync i)
      | _ => none
    | none => none
  | .rename q => match x.prog.posts q with
    | some y => match y.stage with
      | .synced _ => some (.rename (tempName q) (finalName q))
      | _ => none
    | none => none
  | .place q => match x.prog.posts q with
    | some y => match y.stage with
      | .final _ => some .syncDir
      | _ => none
    | none => none
  | .commit _ c =>
    some (.append x.prog.journal (commitFrame x.prog.key (x.prog.records ++ backOf x.prog) c))
  | .publish => x.prog.committing.map fun _ => .sync x.prog.journal
  | .clean q f => some (.remove (if f then finalName q else tempName q))
  | _ => none

/-- **A command's operation is what it does to the file system.** -/
theorem opOf_after (x : St) (c : Cmd) :
    (x.after c).fs = match opOf x c with
      | some op => (x.fs.step op).1
      | none => x.fs := by
  cases c with
  | create q | write q _ | sync q | rename q | place q =>
    simp only [St.after, opOf]
    cases x.prog.posts q with
    | none => rfl
    | some y =>
      obtain ⟨o, w, st⟩ := y
      cases st <;> rfl
  | publish =>
    simp only [St.after, opOf]
    cases x.prog.committing <;> rfl
  | refuse q =>
    simp only [St.after, opOf]
    cases x.prog.posts q <;> rfl
  | _ => rfl

/-- What a command leaves when its operation fails, in each way `Fs.failures` lists. -/
def failsAll (x : St) : Cmd → List St
  | .write q m => match x.prog.posts q with
    | some y => match y.stage with
      | .writing i => (x.fs.failures (.append i (y.chunk m))).map (x.refusedAt q)
      | _ => []
    | none => []
  | .commit q c =>
    (x.fs.failures
        (.append x.prog.journal (commitFrame x.prog.key (x.prog.records ++ backOf x.prog) c))).map
      fun t => ⟨t, { x.prog.set q none with committing := some c, accepting := false },
        { x.hist with appended := x.hist.appended ++ [(x.prog.run, c)] }⟩
  | c => x.fails c

/-- **What a command allowed leaves when its operation fails is a step of the store.** -/
theorem failsAll_step (cfg : Config) (x : St) (c : Cmd) (h : c.allowed cfg x = true) (u : St)
    (hu : u ∈ failsAll x c) : Step cfg x.fs x.prog x.hist u.fs u.prog u.hist := by
  have ha := allowed_sound cfg x c h
  cases c with
  | write q m =>
    obtain ⟨y, i, hq, hs⟩ := ha
    simp only [failsAll, hq, hs, List.mem_map] at hu
    obtain ⟨t, ht, rfl⟩ := hu
    simp only [St.refusedAt, hq]
    exact .writeFails _ _ _ q y i m t hq hs ht
  | commit q c =>
    obtain ⟨y, i, hq, hs, hc, hac, hseq, hsize, hcrc, hok, hg⟩ := ha
    simp only [failsAll, backOf, hc, List.append_nil, List.mem_map] at hu
    obtain ⟨t, ht, rfl⟩ := hu
    exact .commitFails _ _ _ q y i c t hq hs hc hac hseq hsize hcrc hok hg ht
  | reserve | create | sync | rename | place | publish | refuse | clean | drop =>
    exact fails_step cfg x _ ha u hu

/-- **A command's failure leaves its operation failed**: what an allowed command leaves of the file
system when it fails is what `Fs.failures` lists for its operation. -/
theorem failsAll_op (cfg : Config) (x : St) (c : Cmd) (h : c.allowed cfg x = true) (u : St)
    (hu : u ∈ failsAll x c) : ∃ op, opOf x c = some op ∧ u.fs ∈ x.fs.failures op := by
  have ha := allowed_sound cfg x c h
  cases c with
  | create q =>
    obtain ⟨y, hq, _⟩ := ha
    simp only [failsAll, St.fails, List.mem_map] at hu
    obtain ⟨t, ht, rfl⟩ := hu
    exact ⟨.create (tempName q), by simp [opOf, hq], by simpa [St.refusedAt, hq] using ht⟩
  | write q m =>
    obtain ⟨y, i, hq, hs⟩ := ha
    simp only [failsAll, hq, hs, List.mem_map] at hu
    obtain ⟨t, ht, rfl⟩ := hu
    exact ⟨.append i (y.chunk m), by simp [opOf, hq, hs], by simpa [St.refusedAt, hq] using ht⟩
  | sync q =>
    obtain ⟨y, i, hq, hs, _⟩ := ha
    simp only [failsAll, St.fails, hq, hs, List.mem_map] at hu
    obtain ⟨t, ht, rfl⟩ := hu
    exact ⟨.sync i, by simp [opOf, hq, hs], by simpa [St.stoppedAt, hq] using ht⟩
  | rename q =>
    obtain ⟨y, i, hq, hs⟩ := ha
    simp only [failsAll, St.fails, List.mem_map] at hu
    obtain ⟨t, ht, rfl⟩ := hu
    exact ⟨.rename (tempName q) (finalName q), by simp [opOf, hq, hs],
      by simpa [St.refusedAt, hq] using ht⟩
  | place q =>
    obtain ⟨y, i, hq, hs, _⟩ := ha
    simp only [failsAll, St.fails, List.mem_map] at hu
    obtain ⟨t, ht, rfl⟩ := hu
    exact ⟨.syncDir, by simp [opOf, hq, hs], by simpa [St.untrustedAt, hq] using ht⟩
  | commit q c =>
    simp only [failsAll, List.mem_map] at hu
    obtain ⟨t, ht, rfl⟩ := hu
    exact ⟨_, rfl, ht⟩
  | publish =>
    obtain ⟨c, hc, _⟩ := ha
    simp only [failsAll, St.fails, List.mem_map] at hu
    obtain ⟨t, ht, rfl⟩ := hu
    exact ⟨.sync x.prog.journal, by simp [opOf, hc], ht⟩
  | clean q f =>
    simp only [failsAll, St.fails, List.mem_map] at hu
    obtain ⟨t, ht, rfl⟩ := hu
    exact ⟨_, rfl, ht⟩
  | reserve | refuse | drop => simp [failsAll, St.fails] at hu

theorem map_fs (l : List Fs) (f : Fs → St) (hf : ∀ t, (f t).fs = t) : l.map (St.fs ∘ f) = l := by
  induction l <;> simp_all

/-- **What a command's failures leave of the file system, in order, is what `Fs.failures` lists for
its operation**, so that the `K`-th outcome of the one is the `K`-th of the other. -/
theorem failsAll_fs (cfg : Config) (x : St) (c : Cmd) (h : c.allowed cfg x = true) (op : Op)
    (hop : opOf x c = some op) : (failsAll x c).map St.fs = x.fs.failures op := by
  have ha := allowed_sound cfg x c h
  cases c with
  | create q =>
    obtain ⟨y, hq, _⟩ := ha
    simp only [opOf, hq, Option.map_some, Option.some.injEq] at hop
    subst hop
    simp only [failsAll, St.fails, List.map_map]
    exact map_fs _ _ fun t => by simp [St.refusedAt, hq]
  | write q m =>
    obtain ⟨y, i, hq, hs⟩ := ha
    simp only [opOf, hq, hs, Option.some.injEq] at hop
    subst hop
    simp only [failsAll, hq, hs, List.map_map]
    exact map_fs _ _ fun t => by simp [St.refusedAt, hq]
  | sync q =>
    obtain ⟨y, i, hq, hs, _⟩ := ha
    simp only [opOf, hq, hs, Option.some.injEq] at hop
    subst hop
    simp only [failsAll, St.fails, hq, hs, List.map_map]
    exact map_fs _ _ fun t => by simp [St.stoppedAt, hq]
  | rename q =>
    obtain ⟨y, i, hq, hs⟩ := ha
    simp only [opOf, hq, hs, Option.some.injEq] at hop
    subst hop
    simp only [failsAll, St.fails, List.map_map]
    exact map_fs _ _ fun t => by simp [St.refusedAt, hq]
  | place q =>
    obtain ⟨y, i, hq, hs, _⟩ := ha
    simp only [opOf, hq, hs, Option.some.injEq] at hop
    subst hop
    simp only [failsAll, St.fails, List.map_map]
    exact map_fs _ _ fun t => by simp [St.untrustedAt, hq]
  | commit q c =>
    simp only [opOf, Option.some.injEq] at hop
    subst hop
    simp only [failsAll, List.map_map]
    exact map_fs _ _ fun t => rfl
  | publish =>
    obtain ⟨c, hc, _⟩ := ha
    simp only [opOf, hc, Option.map_some, Option.some.injEq] at hop
    subst hop
    simp only [failsAll, St.fails, List.map_map]
    exact map_fs _ _ fun t => rfl
  | clean q f =>
    simp only [opOf, Option.some.injEq] at hop
    subst hop
    simp only [failsAll, St.fails, List.map_map]
    exact map_fs _ _ fun t => rfl
  | reserve | refuse | drop => simp [opOf] at hop

/-! ## Cases -/

/-- The directory as a crash left it: each name and file synced, the files numbered in its order. -/
def ofImage (img : List (Bytes × Bytes)) : Fs :=
  ⟨((List.range img.length).zip img).map fun p => ⟨p.2.1, some p.1, []⟩,
    ((List.range img.length).zip img).map fun p => (p.1, Data.empty.after p.2.2), img.length, true⟩

theorem ofImage_files (img : List (Bytes × Bytes)) (p : Ino × Data) (hp : p ∈ (ofImage img).files) :
    ∃ i n o, (i, (n, o)) ∈ (List.range img.length).zip img ∧ p = (i, Data.empty.after o) := by
  simp only [ofImage, List.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  exact ⟨q.1, q.2.1, q.2.2, hq, rfl⟩

/-- **A start on an image is on a settled file system**, as a crash leaves (`crash_settles`). -/
theorem ofImage_settled (img : List (Bytes × Bytes)) : (ofImage img).Settled := by
  refine ⟨rfl, fun e he => ?_, fun p hp => ?_, fun p hp => ?_⟩
  · simp only [ofImage, List.mem_map] at he
    obtain ⟨q, _, rfl⟩ := he
    exact ⟨rfl, rfl⟩
  · obtain ⟨i, n, o, _, rfl⟩ := ofImage_files img p hp
    exact DN.News.FsModel.after_settled _ _
  · obtain ⟨i, n, o, hm, rfl⟩ := ofImage_files img p hp
    simp only [Fs.holds, List.any_eq_true]
    refine ⟨⟨n, some i, []⟩, ?_, by simp [Entry.holds, Entry.Leaves]⟩
    simp only [ofImage, List.mem_map]
    exact ⟨(i, (n, o)), hm, rfl⟩

/-- **A start on an image is one `Reach` may begin** (`reach_startOn`): its syncs are trusted, and
its journal holds nothing past what is kept. -/
theorem ofImage_startable (k : Bytes) (img : List (Bytes × Bytes)) :
    DN.News.StoreRun.startable k (ofImage img) = true := by
  have hd : ∀ i d, (ofImage img).data i = some d → d.trusted = true ∧ d.kept = d.seen := by
    intro i d h
    simp only [Fs.data, DN.News.FsModel.lookup_eq_find, Option.map_eq_some_iff] at h
    obtain ⟨p, hp, rfl⟩ := h
    obtain ⟨_, _, o, _, rfl⟩ := ofImage_files img p (List.mem_of_find?_eq_some hp)
    exact ⟨rfl, rfl⟩
  have hdt : (ofImage img).dirTrusted = true := rfl
  simp only [DN.News.StoreRun.startable, DN.News.StoreRun.trusted,
    DN.News.StoreRun.startChecked, hdt, Bool.true_and, Bool.and_eq_true]
  cases hl : (ofImage img).lookup journalName with
  | none => simp
  | some i =>
    cases hdd : (ofImage img).data i with
    | none => simp [hdd]
    | some d =>
      obtain ⟨ht, hk⟩ := hd i d hdd
      simp [hdd, ht, hk]

/-- An operation in `dn-compiler fs-model`'s words. -/
def opText : Op → String
  | .create n => s!"create:{hex n}"
  | .open_ n => s!"open:{hex n}"
  | .append i o => s!"append:{i}:{hex o}"
  | .truncate i n => s!"truncate:{i}:{n}"
  | .sync i => s!"sync:{i}"
  | .read i o n => s!"read:{i}:{o}:{n}"
  | .size i => s!"size:{i}"
  | .rename a b => s!"rename:{hex a}:{hex b}"
  | .remove n => s!"remove:{hex n}"
  | .syncDir => "sync-dir"
  | .list => "list"

def parseGroup (s : String) : Option Group :=
  match s.splitOn "=" with
  | [n, k] => do pure ⟨← parseOctets n, ← natOf k⟩
  | _ => none

def parseCmd (s : String) : Option Cmd :=
  match s.splitOn ":" with
  | ["reserve", o] => do pure (.reserve (← parseOctets o))
  | ["create", q] => do pure (.create (← natOf q))
  | ["write", q, m] => do pure (.write (← natOf q) (← natOf m))
  | ["sync", q] => do pure (.sync (← natOf q))
  | ["rename", q] => do pure (.rename (← natOf q))
  | ["place", q] => do pure (.place (← natOf q))
  | ["commit", q, seq, mid, gs, hdr, size, crc] => do
    pure (.commit (← natOf q) ⟨← natOf seq, ← parseOctets mid, ← (← items "," gs).mapM parseGroup,
      ← natOf hdr, ← natOf size, ← natOf crc⟩)
  | ["publish"] => some .publish
  | ["refuse", q] => do pure (.refuse (← natOf q))
  | ["clean", q, "0"] => do pure (.clean (← natOf q) false)
  | ["clean", q, "1"] => do pure (.clean (← natOf q) true)
  | ["drop", q] => do pure (.drop (← natOf q))
  | _ => none

/-- An event of a run: a command, and the outcome its operation fails with, if it does; or the
process ending and a new start on the file system as it is, its `N`-th operation failing with the
`K`-th outcome, if it does. -/
inductive Event
  | cmd (c : Cmd) (k : Option Nat)
  | restart (fails : Option (Nat × Nat))

def parseEvent (s : String) : Option Event :=
  match s.splitOn ":" with
  | ["restart"] => some (.restart none)
  | ["restart", i, k] => do pure (.restart (some (← natOf i, ← natOf k)))
  | _ =>
    match s.splitOn "!" with
    | [c] => do pure (.cmd (← parseCmd c) none)
    | [c, k] => do pure (.cmd (← parseCmd c) (some (← natOf k)))
    | _ => none

def opsText (ops : List (Op × Option Nat)) : String :=
  joined ";" (ops.map fun p => opText p.1 ++ (p.2.map fun k => s!"!{k}").getD "")

/-- The events done in turn from `x`, the program running if `up`, the `n`-th first, the operations
of those before in `done`: what the line answers, or why it is not a case. A start begins only where
`Reach` may begin one (`startable`). -/
def events (cfg : Config) (force : Bool) :
    St → Bool → List Event → Nat → List String → Except String String
  | x, _, [], _, done =>
    .ok s!"ok {"|".intercalate done.reverse} {imageText (sortedImage x.fs.image)}"
  | x, up, .cmd c k :: rest, n, done =>
    if !up || !(force || c.allowed cfg x) then .ok s!"not-allowed {n}"
    else match k with
      | none => events cfg force (x.after c) true rest (n + 1)
          (opsText ((opOf x c).toList.map (·, none)) :: done)
      | some k => match (failsAll x c)[k]?, opOf x c with
        | some u, some op => events cfg force u true rest (n + 1) (opsText [(op, some k)] :: done)
        | _, _ => .error s!"no outcome {k} of event {n}"
  | x, _, .restart f :: rest, n, done =>
    if !DN.News.StoreRun.startable x.prog.key x.fs then .ok s!"not-startable {n}"
    else
      let s := x.fs
      let r := x.prog.run + 1
      match recover cfg (image (startSyncs s)) with
      | .error e => .ok s!"corrupt {faultText e}"
      | .ok _ =>
        let ops := startOps cfg s
        match f with
        | none =>
          match startOn cfg s x.hist r with
          | some y => events cfg force y true rest (n + 1) (opsText (ops.map (·, none)) :: done)
          | none => .error s!"no start at event {n}"
        | some (i, k) =>
          match ops[i]? with
          | some op =>
            match ((s.run (ops.take i)).failures op)[k]? with
            | some t => events cfg force ⟨t, { x.prog with run := r }, x.hist⟩ false rest (n + 1)
                (opsText ((ops.take i).map (·, none) ++ [(op, some k)]) :: done)
            | none => .error s!"no outcome {k} of event {n}"
          | none => .error s!"no operation {i} in the start of event {n}"

/-- The answer to one case, or why the line is not one. -/
def answer (line : String) : Except String String :=
  match line.splitOn " " with
  | [mode, key, groups, run, img, evs] =>
    match (mode == "run" || mode == "force"), parseOctets key,
        (items "," groups).bind (·.mapM parseOctets), natOf run, DN.News.FsCases.parseImage img,
        (items ";" evs).bind (·.mapM parseEvent) with
    | true, some k, some gs, some r, some i, some es =>
      let cfg : Config := ⟨gs, k⟩
      let s := ofImage i
      match recover cfg (image (startSyncs s)) with
      | .error f => .ok s!"corrupt {faultText f}"
      | .ok _ =>
        match startOn cfg s Hist.empty r with
        | some x =>
          events cfg (mode == "force") x true es 1 [opsText ((startOps cfg s).map (·, none))]
        | none => .error s!"no start: {line}"
    | _, _, _, _, _, _ => .error s!"not a case: {line}"
  | _ => .error s!"not a case: {line}"

def runAll (input : String) : Except String String := do
  let lines := (input.splitOn "\n").filter (!·.isEmpty)
  let answers ← lines.mapM answer
  pure (String.join (answers.map (· ++ "\n")))

end DN.News.StoreCases
