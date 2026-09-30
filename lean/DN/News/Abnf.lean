-- SPDX-License-Identifier: AGPL-3.0-or-later

/-!
# DN.News.Abnf

What a grammar in ABNF (RFC 5234) matches, as a set of positions. A term is what one rule's
definition says; rules refer to each other by their place in the grammar, so a grammar may be
recursive, as comments nest in RFC 5322.

`endsFrom g input fuel t p` is the set of positions a match of `t` starting at `p` can end at: all
of them, since ABNF is not ordered choice, so an alternative or a repetition that could stop at
several places keeps them all. What a rule matches from a position depends on nothing else, so
the answer is kept (`Memo`) and worked out once, as a chart parser does; the grammars of RFC 5322
are ambiguous enough that without it the work grows with the cube of the input.

Each nested term takes one unit of `fuel`; running out of it stops the run (`Stop.fuel`) rather
than answering, and so does a reference to a rule the grammar lacks (`Stop.noRule`). A repetition
runs as a loop and spends no fuel on its length. Left recursion, a rule reached again at the
position it started from, would spend fuel without end; the grammars here have none, which
`scripts/gen_abnf.py` checks, and it counts the most terms a match goes through at one position
(`AbnfRules.depth`). A chain of nested matches goes through at most that many at each position of
the input, and positions only grow down the chain, so `fuel` gives enough for any input.
-/

namespace DN.News.Abnf

inductive Term where
  /-- One byte from `lo` to `hi`. -/
  | range (lo hi : Nat)
  /-- A quoted string: an ASCII letter matches in either case (RFC 5234 §2.3). -/
  | text (s : String)
  /-- Numeric values in sequence, `%d112.111`: every byte as written. -/
  | exact (s : List Nat)
  /-- The rule at this place in the grammar. -/
  | ref (i : Nat)
  | seq (ts : List Term)
  | alt (ts : List Term)
  /-- From `lo` to `hi` matches of `t` in a row; `none` for no upper bound. -/
  | rep (lo : Nat) (hi : Option Nat) (t : Term)
  deriving Inhabited

/-- A set of positions, ascending and without repeats. -/
abbrev Pos := List Nat

/-- The positions of both sets, merged in one pass; `n` bounds the steps, one per position. -/
def mergeUp : Nat → Pos → Pos → Pos
  | 0, a, b => a ++ b
  | _ + 1, [], b => b
  | _ + 1, a, [] => a
  | n + 1, p :: ps, q :: qs =>
    if p < q then p :: mergeUp n ps (q :: qs)
    else if q < p then q :: mergeUp n (p :: ps) qs
    else p :: mergeUp n ps qs

def union (a b : Pos) : Pos := mergeUp (a.length + b.length) a b

/-- The positions of `a` that are not in `b`, in one pass. -/
def minusUp : Nat → Pos → Pos → Pos
  | 0, a, _ => a
  | _ + 1, [], _ => []
  | _ + 1, a, [] => a
  | n + 1, p :: ps, q :: qs =>
    if p < q then p :: minusUp n ps (q :: qs)
    else if q < p then minusUp n (p :: ps) qs
    else minusUp n ps qs

def minus (a b : Pos) : Pos := minusUp (a.length + b.length) a b

/-- ASCII lower case. -/
def lower (b : Nat) : Nat := if 65 ≤ b ∧ b ≤ 90 then b + 32 else b

/-- Whether `s` is at `p` in `input`, comparing each byte through `norm`. -/
def at? (input : Array Nat) (norm : Nat → Nat) : Nat → List Nat → Bool
  | _, [] => true
  | p, c :: cs =>
    match input[p]? with
    | some b => norm b == norm c && at? input norm (p + 1) cs
    | none => false

/-- The bytes of an ASCII string. -/
def codes (s : String) : List Nat := s.toList.map Char.toNat

/-- Whether every position of `next` lies past the greatest of `down`, a set in descending
order. -/
def beyond (next down : Pos) : Bool :=
  match next, down with
  | q :: _, top :: _ => top < q
  | _, _ => true

/-- Where a match of each rule from each position ends, as far as that has been worked out: for
each position, the rules and their ends. -/
abbrev Memo := Array (List (Nat × Pos))

/-- Why a run stopped without an answer. -/
inductive Stop where
  | fuel
  | noRule (i : Nat)

abbrev Run := ExceptT Stop (StateM Memo)

def endsFrom (g : Array Term) (input : Array Nat) : Nat → Term → Nat → Run Pos
  | 0, _, _ => throw .fuel
  | f + 1, t, p =>
    -- The ends of a match of `u` from any position of `S`.
    let fromAll (u : Term) (S : Pos) : Run Pos :=
      S.foldlM (fun R q => union R <$> endsFrom g input f u q) []
    match t with
    | .range lo hi =>
      pure (match input[p]? with
        | some b => if lo ≤ b ∧ b ≤ hi then [p + 1] else []
        | none => [])
    | .text s =>
      let cs := codes s
      pure (if at? input lower p cs then [p + cs.length] else [])
    | .exact s => pure (if at? input id p s then [p + s.length] else [])
    | .ref i => do
      match ((← get)[p]?.getD []).lookup i with
      | some e => pure e
      | none =>
        match g[i]? with
        | none => throw (.noRule i)
        | some u =>
          let e ← endsFrom g input f u p
          modify fun m => m.modify p ((i, e) :: ·)
          pure e
    | .seq ts => ts.foldlM (fun R u => fromAll u R) [p]
    | .alt ts => ts.foldlM (fun R u => union R <$> endsFrom g input f u p) []
    | .rep lo hi u => do
      -- Each round matches `u` once more from the positions the last round reached. After `lo`
      -- rounds every position reached counts; a round that reaches nothing new ends the loop,
      -- and none can go on longer than the input has positions.
      -- The positions counted so far are kept in descending order, so that the usual round,
      -- whose positions all lie past them, adds its own without merging.
      let mut count := 0
      let mut frontier : Pos := [p]
      let mut seenDown : List Nat := if lo = 0 then [p] else []
      for _ in [0:lo + input.size + 1] do
        if hi.any (· ≤ count) || frontier.isEmpty then break
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
      pure seenDown.reverse

/-- Fuel enough for a grammar whose matches go at most `depth` terms deep at one position, the
reference a run starts with counted, on an input of `n` bytes: `depth` at each of its `n + 1`
positions. -/
def fuel (depth n : Nat) : Nat := depth * (n + 1)

/-- Whether rule `i` of `g`, a grammar `depth` terms deep at one position, matches all of `bytes`,
or why the run stopped. -/
def matches? (g : Array Term) (depth i : Nat) (bytes : List Nat) : Except Stop Bool :=
  let input := bytes.toArray
  let memo : Memo := Array.replicate (input.size + 1) []
  ((endsFrom g input (fuel depth input.size) (.ref i) 0).run.run' memo).map (·.contains input.size)

end DN.News.Abnf
