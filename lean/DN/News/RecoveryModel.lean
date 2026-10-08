-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.RecoveryMutant
import DN.News.JournalModel

/-!
# DN.News.RecoveryModel

Recovery (`DN.News.Recovery`) run on cases, as `dn-compiler recovery-model` answers them, a line
each; octets are hex, `-` for none:

    recover KEY GROUPS IMAGE   what recovery finds, the key of a journal it would create KEY,
                               the groups the store carries GROUPS (`NAME,NAME`), the directory
                               IMAGE (`NAME=OCTETS;NAME=OCTETS`, in the order it lists them)
    apply IMAGE ACTIONS        the directory once ACTIONS are done and durable

A finding reads as `corrupt WHY`, why the store does not start — corruption, or `too-many`,
`exhausted` or `bad-key`, which are not — or `ok KEY NEXT END ARTICLES ASIDE ACTIONS`: the journal's
key, the next sequence number, where the journal ends, its commits (`C:…` as `dn-compiler
journal-model` writes them, separated by `;`), the numbers of the files set aside (`N,N`) and the
actions (`keep:NAME:OCTETS`, `rename:NAME:NAME`, `remove:NAME`, `sync-dir`, `cut:N`, `create:KEY`,
separated by `;`). With a mutant, recovery follows its rules.
-/

namespace DN.News.RecoveryModel

open DN.News.Journal
open DN.News.Recovery
open DN.News.RecoveryMutant (recoverM)
open DN.News.FrameModel (parseHex hex)
open DN.News.JournalModel (natOf recordText whyText)
open DN.News.CommandSpec (ascii)

def faultText : Fault → String
  | .badName n => s!"bad-name {hex n}"
  | .noJournal => "no-journal"
  | .journal at_ w => s!"journal {at_} {whyText w}"
  | .seqTwice s => s!"seq-twice {s}"
  | .numberNotAbove g n => s!"number-not-above {hex g} {n}"
  | .unknownGroup g => s!"unknown-group {hex g}"
  | .missingFile s => s!"missing-file {s}"
  | .wrongSize s => s!"wrong-size {s}"
  | .exhausted => "exhausted"
  | .badKey => "bad-key"
  | .tooMany n => s!"too-many {n}"

def actionText : Action → String
  | .keep n o => s!"keep:{hex n}:{hex o}"
  | .rename a b => s!"rename:{hex a}:{hex b}"
  | .remove n => s!"remove:{hex n}"
  | .syncDir => "sync-dir"
  | .cut n => s!"cut:{n}"
  | .create k => s!"create:{hex k}"

/-- Items joined by `sep`, or `-` for none. -/
def joined (sep : String) (xs : List String) : String :=
  if xs.isEmpty then "-" else sep.intercalate xs

def imageText (img : Image) : String :=
  joined ";" (img.map fun p => s!"{hex p.1}={hex p.2}")

def findingText : Except Fault (Store × List Action) → String
  | .error f => s!"corrupt {faultText f}"
  | .ok (st, acts) =>
    s!"ok {hex st.key} {st.next} {st.journalEnd} " ++
      s!"{joined ";" (st.articles.map (recordText ∘ .commit))} " ++
      s!"{joined "," (st.setAside.map toString)} {joined ";" (acts.map actionText)}"

/-- Items of a list written with `sep`, or none for `-`; no item may be empty. -/
def items (sep : String) (s : String) : Option (List String) :=
  if s == "-" then some []
  else
    let xs := s.splitOn sep
    if xs.any (·.isEmpty) then none else some xs

/-- A directory, each name once. -/
def parseImage (s : String) : Option Image := do
  let img ← (← items ";" s).mapM fun p =>
    match p.splitOn "=" with
    | [n, o] => do pure (← parseHex n, ← parseHex o)
    | _ => none
  if (img.map (·.1)).Nodup then some img else none

def parseAction (s : String) : Option Action :=
  match s.splitOn ":" with
  | ["keep", n, o] => do pure (.keep (← parseHex n) (← parseHex o))
  | ["rename", a, b] => do pure (.rename (← parseHex a) (← parseHex b))
  | ["remove", n] => do pure (.remove (← parseHex n))
  | ["sync-dir"] => some .syncDir
  | ["cut", n] => do pure (.cut (← natOf n))
  | ["create", k] => do
    let key ← parseHex k
    if key.length = keyLength then some (.create key) else none
  | _ => none

/-- The answer to one case, or why the line is not one. -/
def answer (m : RecoveryMutant.Mutant) (line : String) : Except String String :=
  match line.splitOn " " with
  | ["recover", key, groups, image] =>
    match parseHex key, (items "," groups).bind (·.mapM parseHex), parseImage image with
    | some k, some gs, some img => .ok (findingText (recoverM m ⟨gs, k⟩ img))
    | _, _, _ => .error s!"not a case: {line}"
  | ["apply", image, actions] =>
    match parseImage image, (items ";" actions).bind (·.mapM parseAction) with
    | some img, some acts => .ok (imageText (applyAll img acts))
    | _, _ => .error s!"not a case: {line}"
  | _ => .error s!"not a case: {line}"

def runAll (m : RecoveryMutant.Mutant) (input : String) : Except String String := do
  let lines := (input.splitOn "\n").filter (!·.isEmpty)
  let answers ← lines.mapM (answer m)
  pure (String.join (answers.map (· ++ "\n")))

end DN.News.RecoveryModel
