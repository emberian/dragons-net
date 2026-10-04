-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.FsMutant
import DN.News.RecoveryModel

/-!
# DN.News.FsCases

The model of the file system (`DN.News.FsModel`) run on cases, as `dn-compiler fs-model` answers
them, a line each; octets are hex, `-` for none, files numbered as they are created, from 0:

    run OPS            what each operation answers, and what the program then finds
    crash OPS IMAGE    whether a crash after the operations may leave IMAGE: yes or no
    crashes OPS        the images `Fs.crashes` lists after them, with the octets `Data.cuts` gives

OPS is `-` or operations separated by `;`: `create:NAME`, `open:NAME`, `append:FILE:OCTETS`,
`truncate:FILE:SIZE`, `sync:FILE`, `read:FILE:OFFSET:LENGTH`, `size:FILE`, `rename:NAME:NAME`,
`remove:NAME`, `sync-dir`, `list`; one followed by `!K` fails, leaving the `K`-th of the outcomes
`Fs.failures` lists from 0 (an append, its first `K` octets; a sync, 0 alone, after which no later
sync of it is trusted; another, 0 nothing and 1 all). An answer is `done`, `file:FILE`,
`bytes:OCTETS`, `size:N`, `names:NAME,NAME`, `exists`, `missing` or `failed`; an image is
`NAME=OCTETS;NAME=OCTETS`. Answers list names in the order of their octets in hex, not the
directory's. With a mutant, the model follows its rules.
-/

namespace DN.News.FsCases

open DN.News.FsModel
open DN.News.FsMutant (Mutant runM mayLeaveM)
open DN.News.FsLeaves (Image)
open DN.News.FrameModel (parseHex hex)
open DN.News.JournalModel (natOf)
open DN.News.RecoveryModel (joined items imageText)

/-- Names in the order of their octets in hex. -/
def sortedNames (ns : List Bytes) : List String := (ns.map hex).mergeSort fun a b => decide (a ≤ b)

/-- An image in the order of its names' octets in hex. -/
def sortedImage (img : Image) : Image := img.mergeSort fun a b => decide (hex a.1 ≤ hex b.1)

def resultText : Option Result → String
  | some .done => "done"
  | some (.file i) => s!"file:{i}"
  | some (.bytes bs) => s!"bytes:{hex bs}"
  | some (.size n) => s!"size:{n}"
  | some (.names ns) => s!"names:{joined "," (sortedNames ns)}"
  | some .exists_ => "exists"
  | some .missing => "missing"
  | none => "failed"

/-- Octets in hex, `-` for none; nothing else, the empty text among it. -/
def parseOctets (s : String) : Option Bytes := if s.isEmpty then none else parseHex s

def parseOp (s : String) : Option Op :=
  match s.splitOn ":" with
  | ["create", n] => do pure (.create (← parseOctets n))
  | ["open", n] => do pure (.open_ (← parseOctets n))
  | ["append", i, o] => do pure (.append (← natOf i) (← parseOctets o))
  | ["truncate", i, n] => do pure (.truncate (← natOf i) (← natOf n))
  | ["sync", i] => do pure (.sync (← natOf i))
  | ["read", i, o, n] => do pure (.read (← natOf i) (← natOf o) (← natOf n))
  | ["size", i] => do pure (.size (← natOf i))
  | ["rename", a, b] => do pure (.rename (← parseOctets a) (← parseOctets b))
  | ["remove", n] => do pure (.remove (← parseOctets n))
  | ["sync-dir"] => some .syncDir
  | ["list"] => some .list
  | _ => none

/-- An operation, and the outcome it fails with, if it does. -/
def parseStep (s : String) : Option (Op × Option Nat) :=
  match s.splitOn "!" with
  | [op] => do pure (← parseOp op, none)
  | [op, k] => do pure (← parseOp op, some (← natOf k))
  | _ => none

def parseOps (s : String) : Option (List (Op × Option Nat)) := do
  (← items ";" s).mapM parseStep

/-- An image, each name once. -/
def parseImage (s : String) : Option Image := do
  let img ← (← items ";" s).mapM fun p =>
    match p.splitOn "=" with
    | [n, o] => do pure (← parseOctets n, ← parseOctets o)
    | _ => none
  if (img.map (·.1)).Nodup then some img else none

/-- An image in the directory's order, if each of its names is one of the directory's. -/
def ordered (s : Fs) (img : Image) : Option Image :=
  if img.all fun p => s.dir.any (·.name == p.1) then
    some (s.dir.filterMap fun e => (img.lookup e.name).map (e.name, ·))
  else none

/-- The answer to one case, or why the line is not one. -/
def answer (m : Mutant) (line : String) : Except String String :=
  match line.splitOn " " with
  | ["run", ops] =>
    match (parseOps ops).bind (runM m Fs.empty) with
    | some (rs, s) => .ok s!"{joined ";" (rs.map resultText)} {imageText (sortedImage s.image)}"
    | none => .error s!"not a case: {line}"
  | ["crash", ops, img] =>
    match (parseOps ops).bind (runM m Fs.empty), parseImage img with
    | some (_, s), some i =>
      .ok (if (ordered s i).any (mayLeaveM m s) then "yes" else "no")
    | _, _ => .error s!"not a case: {line}"
  | ["crashes", ops] =>
    match (parseOps ops).bind (runM m Fs.empty) with
    | some (_, s) =>
      .ok (joined " "
        ((s.crashes Data.cuts).map fun t => imageText (sortedImage t.image)).eraseDups)
    | none => .error s!"not a case: {line}"
  | _ => .error s!"not a case: {line}"

def runAll (m : Mutant) (input : String) : Except String String := do
  let lines := (input.splitOn "\n").filter (!·.isEmpty)
  let answers ← lines.mapM (answer m)
  pure (String.join (answers.map (· ++ "\n")))

end DN.News.FsCases
