-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.AbnfProg

/-!
# DN.News.AbnfOrder

What the proofs of the rules' functions take from this grammar, worked out once by the kernel (`facts`): each
function calls only functions before it, every rule with a function has one, a function's frame lies past its
callers' slots, and `gen` reaches every leaf within its steps.
-/

namespace DN.News.AbnfOrder

open DN.News.Abnf DN.News.AbnfProg DN.News.AbnfRules

/-- Whether `gen`, given `f` steps, works `t` out to its leaves and calls, its parts' by `g`, and a repetition's
bounds are small enough for the words that count its rounds. -/
def enoughAt (g : Term → Bool) : Option Leaf → Term → Bool
  | some _, _ => true
  | none, .seq ts | none, .alt ts => ts.all g
  | none, .rep lo hi u => decide (lo < 2 ^ 32) && hi.all (· < 2 ^ 32) && g u
  | none, _ => true

def enough : Nat → Term → Bool
  | 0, _ => false
  | f + 1, t => enoughAt (enough f) (leafOf t) t

/-- The functions in order: each calls only those before it, is a rule's and has a frame past the slots its callers
use; every rule with a function is among them, once; `gen` has steps enough for each. -/
theorem facts : ordered = true ∧ order.Nodup ∧
    order.all (fun i => decide (i < grammar.size) && decide (roots ≤ frameOf i) &&
      (i == commentRule || enough steps (termOf i)) &&
      (callees i).all fun j => decide (frameOf i + need i ≤ frameOf j)) = true ∧
    (List.range grammar.size).all (fun i => !hasFun i || order.contains i) = true := by
  decide +kernel

end DN.News.AbnfOrder
