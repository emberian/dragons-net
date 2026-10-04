-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.FsLeaves

/-!
# DN.News.FsMutant

The model of the file system (`DN.News.FsModel`) with one of its rules changed, for the lane that
holds the model against an independent reference to show that it sees each (`scripts/fs_check.py`):
what a crash may leave (`DN.News.FsLeaves.mayLeave`), what a failed operation may have done, and
what a sync does. With no rule changed it is the model (`stepM_none`,
`failuresM_none`, `mayLeaveM_none`), and its runs leave the file system well formed
(`runM_ok`); with any, a run written for it ends otherwise (`mutants_differ`).
-/

namespace DN.News.FsMutant

open DN.News.FsModel
open DN.News.FsLeaves (Image slots mayLeave)

/-- A version of the model with one of its rules changed. -/
inductive Mutant
  | none
  /-- a crash leaves each name as the program sees it, synced or not -/
  | namesAsSeen
  /-- a crash leaves each name as the directory's last sync left it -/
  | namesAsSynced
  /-- a crash leaves each name as synced or as the program sees it, nothing held between -/
  | namesLatestOnly
  /-- a crash may change octets a sync made durable -/
  | keptIgnored
  /-- a crash leaves a file a prefix of what the program sees, never other octets -/
  | prefixOnly
  /-- a crash may leave a file longer than it has been since its last sync -/
  | highIgnored
  /-- a crash may leave one file different octets under two names -/
  | filesApart
  /-- a failed append wrote all its octets or none -/
  | appendAtomic
  /-- a failed sync of a file leaves later ones trusted -/
  | syncFailTrusted
  /-- a failed sync of the directory leaves later ones trusted -/
  | dirSyncFailTrusted
  /-- any other failed operation did nothing -/
  | failsDidNothing
  /-- a sync of a file makes it durable though syncs are not trusted -/
  | untrustedSyncs
  /-- a sync of the directory makes names durable though its syncs are not trusted -/
  | untrustedDirSyncs
  /-- a rename where both names hold the same file removes the first -/
  | renameSameLoses
  /-- a sync of a file leaves the most it may hold as it was -/
  | syncKeepsMost
  /-- a failed append raises the most the file may hold by all its octets -/
  | failedAppendMost
  deriving DecidableEq

def names : List (String × Mutant) :=
  [("names-as-seen", .namesAsSeen), ("names-as-synced", .namesAsSynced),
   ("names-latest-only", .namesLatestOnly), ("kept-ignored", .keptIgnored),
   ("prefix-only", .prefixOnly), ("high-ignored", .highIgnored), ("files-apart", .filesApart),
   ("append-atomic", .appendAtomic), ("sync-fail-trusted", .syncFailTrusted),
   ("dir-sync-fail-trusted", .dirSyncFailTrusted), ("fails-did-nothing", .failsDidNothing),
   ("untrusted-syncs", .untrustedSyncs), ("untrusted-dir-syncs", .untrustedDirSyncs),
   ("rename-same-loses", .renameSameLoses), ("sync-keeps-most", .syncKeepsMost),
   ("failed-append-most", .failedAppendMost)]

/-! ## The model, its rules changed -/

def stepM : Mutant → Fs → Op → Fs × Result
  | .untrustedSyncs, s, .sync i =>
    s.onData i fun d => { d with kept := d.seen, high := d.seen.length }
  | .untrustedDirSyncs, s, .syncDir => ({ s with dir := s.dir.filterMap Entry.settle }, .done)
  | .syncKeepsMost, s, .sync i =>
    s.onData i fun d => if d.trusted then { d with kept := d.seen } else d
  | .renameSameLoses, s, .rename src dst =>
    match s.lookup src with
    | some i => ({ s with dir := rebind (rebind s.dir dst (some i)) src none }, .done)
    | none => (s, .missing)
  | _, s, op => s.step op

def failuresM : Mutant → Fs → Op → List Fs
  | .appendAtomic, s, .append i bs =>
    (List.range (bs.length + 1)).map fun k =>
      (s.step (.append i (if k = bs.length then bs else []))).1
  | .failedAppendMost, s, .append i bs =>
    (List.range (bs.length + 1)).map fun k =>
      (s.onData i fun d =>
        { d.append (bs.take k) with high := max d.high (d.seen.length + bs.length) }).1
  | .syncFailTrusted, s, .sync _ => [s]
  | .dirSyncFailTrusted, s, .syncDir => [s]
  | m, s, op =>
    match op with
    | .append .. | .sync _ | .syncDir => s.failures op
    | op => [s, match m with
      | .failsDidNothing => s
      | m => (stepM m s op).1]

/-- The octets a crash may leave a file holding. -/
def leavesM : Mutant → Data → Bytes → Bool
  | .keptIgnored, d, c => decide (c.length ≤ d.high)
  | .prefixOnly, d, c => d.kept.isPrefixOf c && c.isPrefixOf d.seen
  | .highIgnored, d, c => d.kept.isPrefixOf c
  | _, d, c => d.leaves c

/-- The files a crash may leave a name holding. -/
def choicesM : Mutant → Entry → List (Option Ino)
  | .namesAsSeen, e => [e.seen]
  | .namesAsSynced, e => [e.synced]
  | .namesLatestOnly, e => [e.synced, e.seen]
  | _, e => e.synced :: e.held

def fitsM (m : Mutant) (s : Fs) (ns : List (Option Ino)) (img : Image) : Bool :=
  let sl := (slots s ns).zip img
  (slots s ns).length == img.length &&
    sl.all (fun q => q.1.1 == q.2.1 && leavesM m q.1.2.2 q.2.2) &&
    match m with
    | .filesApart => true
    | _ => sl.all fun q => sl.all fun r => q.1.2.1 != r.1.2.1 || q.2.2 == r.2.2

def mayLeaveM (m : Mutant) (s : Fs) (img : Image) : Bool :=
  s.files.all (fun p => decide (p.2.kept.length ≤ p.2.high)) &&
    (product (s.dir.map (choicesM m))).any fun ns => fitsM m s ns img

/-- Operations, each done or failed as its `k`-th outcome, in order: what each answers (`none` once
failed) and the file system they leave; none when an outcome named is not one. -/
def runM (m : Mutant) : Fs → List (Op × Option Nat) → Option (List (Option Result) × Fs)
  | s, [] => some ([], s)
  | s, (op, none) :: ops =>
    (runM m (stepM m s op).1 ops).map fun r => (some (stepM m s op).2 :: r.1, r.2)
  | s, (op, some k) :: ops =>
    match (failuresM m s op)[k]? with
    | some t => (runM m t ops).map fun r => (none :: r.1, r.2)
    | none => none

/-! ## With no rule changed it is the model -/

theorem stepM_none : stepM .none = Fs.step := by
  funext s op
  cases op <;> rfl

theorem failuresM_none : failuresM .none = Fs.failures := by
  funext s op
  cases op <;> rfl

theorem mayLeaveM_none : mayLeaveM .none = mayLeave := rfl

/-- **The model's runs leave the file system well formed**, so that `mayLeave` decides what a crash
may leave of what they leave (`DN.News.FsLeaves.mayLeave_iff`). -/
theorem runM_ok : ∀ (s : Fs) (ops : List (Op × Option Nat)) (r : List (Option Result) × Fs),
    s.Ok → runM .none s ops = some r → r.2.Ok
  | s, [], r, hs, h => by
    simp only [runM, Option.some.injEq] at h
    exact h ▸ hs
  | s, (op, none) :: ops, r, hs, h => by
    simp only [runM, Option.map_eq_some_iff] at h
    obtain ⟨r', hr', rfl⟩ := h
    rw [stepM_none] at hr'
    exact runM_ok _ ops r' (step_ok s hs op) hr'
  | s, (op, some k) :: ops, r, hs, h => by
    simp only [runM, failuresM_none] at h
    cases ht : (s.failures op)[k]? with
    | none => simp [ht] at h
    | some t =>
      simp only [ht, Option.map_eq_some_iff] at h
      obtain ⟨r', hr', rfl⟩ := h
      exact runM_ok t ops r' (fails_ok s t hs op (List.mem_of_getElem? ht)) hr'

/-! ## Every rule matters -/

/-- What a run shows: what each operation answers, what the program then finds, and whether a crash
may leave `img`. -/
def observe (m : Mutant) (ops : List (Op × Option Nat)) (img : Image) :
    Option (List (Option Result) × Image × Bool) :=
  (runM m Fs.empty ops).map fun r => (r.1, r.2.image, mayLeaveM m r.2 img)

/-- A name of one octet. -/
def nm (b : Nat) : Bytes := [BitVec.ofNat 8 b]

def done (op : Op) : Op × Option Nat := (op, none)

/-- Operations and an image that tell the model with one rule changed from the model. -/
def witness : Mutant → List (Op × Option Nat) × Image
  | .none => ([], [])
  | .namesAsSeen => ([done (.create (nm 97))], [])
  | .namesAsSynced => ([done (.create (nm 97))], [(nm 97, [])])
  | .namesLatestOnly =>
    ([done (.create (nm 97)), done (.create (nm 98)), done (.append 1 (nm 7)),
      done (.rename (nm 97) (nm 98))], [(nm 98, nm 7)])
  | .keptIgnored =>
    ([done (.create (nm 97)), done (.append 0 (nm 1)), done (.sync 0), done .syncDir],
      [(nm 97, nm 2)])
  | .prefixOnly => ([done (.create (nm 97)), done (.append 0 (nm 1))], [(nm 97, nm 0)])
  | .highIgnored => ([done (.create (nm 97)), done .syncDir], [(nm 97, nm 5)])
  | .filesApart =>
    ([done (.create (nm 97)), done .syncDir, done (.append 0 (nm 1)),
      done (.rename (nm 97) (nm 98))], [(nm 97, []), (nm 98, nm 1)])
  | .appendAtomic => ([done (.create (nm 97)), (.append 0 (nm 1 ++ nm 2), some 1)], [])
  | .syncFailTrusted | .untrustedSyncs =>
    ([done (.create (nm 97)), (.sync 0, some 0), done (.append 0 (nm 1)), done (.sync 0),
      done .syncDir], [(nm 97, [])])
  | .dirSyncFailTrusted | .untrustedDirSyncs =>
    ([done (.create (nm 97)), (.syncDir, some 0), done .syncDir], [])
  | .failsDidNothing => ([(.create (nm 97), some 1)], [])
  | .renameSameLoses => ([done (.create (nm 97)), done (.rename (nm 97) (nm 97))], [])
  | .syncKeepsMost =>
    ([done (.create (nm 97)), done (.append 0 (nm 1 ++ nm 2)), done (.sync 0), done .syncDir,
      done (.truncate 0 1), done (.sync 0)], [(nm 97, nm 1 ++ nm 2)])
  | .failedAppendMost =>
    ([done (.create (nm 97)), done .syncDir, (.append 0 (nm 1 ++ nm 2), some 1)],
      [(nm 97, nm 1 ++ nm 2)])

/-- **Each rule of the model changed here matters**: with it changed, its witness ends otherwise. -/
theorem mutants_differ : ∀ m, m ≠ .none →
    observe m (witness m).1 (witness m).2 ≠ observe .none (witness m).1 (witness m).2 := by
  intro m hm
  cases m <;> first | exact absurd rfl hm | decide +kernel

end DN.News.FsMutant
