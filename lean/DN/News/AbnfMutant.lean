-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.Abnf

/-!
# DN.News.AbnfMutant

The interpreter of `DN.News.Abnf` with one of its rules broken, for the lane that holds it
against an independent reading of ABNF to show that it sees each (`scripts/abnf_check.py`). With
no rule broken it is the interpreter (`endsFromM_none`, `matchesM_none`), and each broken rule
changes an answer (`mutants_differ`).
-/

namespace DN.News.AbnfMutant

open DN.News.Abnf

inductive Mutant
  | none
  /-- a quoted string matches only in the case it is written in -/
  | caseSensitive
  /-- an alternation keeps the first alternative that matches, as ordered choice does -/
  | firstAlternative
  /-- a repetition ends only where it goes furthest -/
  | greedyRepetition
  /-- a repetition with an upper bound stops one short of it -/
  | boundOffByOne
  /-- what is kept of a match is looked up by its position alone, not its rule -/
  | memoByPosition
  deriving DecidableEq

def names : List (String × Mutant) :=
  [("case-sensitive", .caseSensitive), ("first-alternative", .firstAlternative),
   ("greedy-repetition", .greedyRepetition), ("bound-off-by-one", .boundOffByOne),
   ("memo-by-position", .memoByPosition)]

def normM (m : Mutant) : Nat → Nat := if m = .caseSensitive then id else lower

def lookupM (m : Mutant) (kept : List (Nat × Pos)) (i : Nat) : Option Pos :=
  if m = .memoByPosition then kept.head?.map (·.2) else kept.lookup i

def altStepM (m : Mutant) (R : Pos) (more : Run Pos) : Run Pos :=
  if m = .firstAlternative ∧ !R.isEmpty then pure R else union R <$> more

def roundsM (m : Mutant) (count : Nat) : Nat := if m = .boundOffByOne then count + 1 else count

def endsM (m : Mutant) (seenDown : List Nat) : Pos :=
  if m = .greedyRepetition then seenDown.take 1 else seenDown.reverse

def endsFromM (m : Mutant) (g : Array Term) (input : Array Nat) : Nat → Term → Nat → Run Pos
  | 0, _, _ => throw .fuel
  | f + 1, t, p =>
    let fromAll (u : Term) (S : Pos) : Run Pos :=
      S.foldlM (fun R q => union R <$> endsFromM m g input f u q) []
    match t with
    | .range lo hi =>
      pure (match input[p]? with
        | some b => if lo ≤ b ∧ b ≤ hi then [p + 1] else []
        | none => [])
    | .text s =>
      let cs := codes s
      pure (if at? input (normM m) p cs then [p + cs.length] else [])
    | .exact s => pure (if at? input id p s then [p + s.length] else [])
    | .ref i => do
      match lookupM m ((← get)[p]?.getD []) i with
      | some e => pure e
      | none =>
        match g[i]? with
        | none => throw (.noRule i)
        | some u =>
          let e ← endsFromM m g input f u p
          modify fun memo => memo.modify p ((i, e) :: ·)
          pure e
    | .seq ts => ts.foldlM (fun R u => fromAll u R) [p]
    | .alt ts => ts.foldlM (fun R u => altStepM m R (endsFromM m g input f u p)) []
    | .rep lo hi u => do
      let mut count := 0
      let mut frontier : Pos := [p]
      let mut seenDown : List Nat := if lo = 0 then [p] else []
      for _ in [0:lo + input.size + 1] do
        if hi.any (· ≤ roundsM m count) || frontier.isEmpty then break
        let next ← fromAll u frontier
        count := count + 1
        if count < lo then
          frontier := next
        else if beyond next seenDown then
          frontier := next
          seenDown := next.reverse ++ seenDown
        else
          let seen := seenDown.reverse
          frontier := minus next seen
          seenDown := (union seen next).reverse
      pure (endsM m seenDown)

def matchesM (m : Mutant) (g : Array Term) (depth i : Nat) (bytes : List Nat) :
    Except Stop Bool :=
  let input := bytes.toArray
  let memo : Memo := Array.replicate (input.size + 1) []
  ((endsFromM m g input (fuel depth input.size) (.ref i) 0).run.run' memo).map
    (·.contains input.size)

theorem endsFromM_none (g : Array Term) (input : Array Nat) :
    endsFromM .none g input = endsFrom g input := by
  funext f
  induction f with
  | zero => rfl
  | succ f ih =>
    funext t p
    -- The two sides differ only in the mutant's choices and in their own copies of each match.
    cases t <;>
      (try simp only [endsFromM, endsFrom, normM, lookupM, altStepM, roundsM, endsM, ih,
        reduceCtorEq, false_and, if_false]) <;> rfl

theorem matchesM_none : matchesM .none = matches? := by
  funext g depth i bytes
  simp only [matchesM, matches?, endsFromM_none]

/-- A grammar and an input on which the mutant's answer is not the interpreter's; rule 0 is
matched. -/
def witness : Mutant → Array Term × String
  | .none => (#[.text "a"], "a")
  | .caseSensitive => (#[.text "a"], "A")
  | .firstAlternative => (#[.seq [.alt [.text "a", .text "ab"], .text "c"]], "abc")
  | .greedyRepetition => (#[.seq [.rep 0 none (.text "a"), .text "ab"]], "aab")
  | .boundOffByOne => (#[.rep 0 (some 2) (.text "a")], "aa")
  | .memoByPosition => (#[.seq [.alt [.ref 1, .ref 2], .text "b"], .text "a", .text "aa"], "aab")

/-- **Each broken rule changes an answer**: on its witness the interpreter matches and the mutant
does not, neither of them stopping short. -/
theorem mutants_differ : ∀ m, m ≠ .none →
    (matches? (witness m).1 8 0 (codes (witness m).2)).toOption = some true ∧
    (matchesM m (witness m).1 8 0 (codes (witness m).2)).toOption = some false := by
  intro m hm
  cases m <;> first | exact absurd rfl hm | decide +kernel

end DN.News.AbnfMutant
