-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.AbnfProg

/-!
# DN.News.AbnfOrder

What the rules' proofs take from this grammar, worked out once by the kernel (`facts`). Each function calls only earlier
ones, and every rule with a function has one. Frames lie past callers' slots, and `gen` reaches every leaf within its
steps.
-/

namespace DN.News.AbnfOrder

open DN.News.Abnf DN.News.AbnfProg DN.News.AbnfRules

/-- Whether `gen`, given `f` steps, works `t` out to its leaves and calls, its parts' by `g`. A repetition's bounds must
also fit the words counting its rounds. -/
def enoughAt (g : Term → Bool) : Option Leaf → Term → Bool
  | some _, _ => true
  | none, .seq ts | none, .alt ts => ts.all g
  | none, .rep lo hi u => decide (lo < 2 ^ 32) && hi.all (· < 2 ^ 32) && g u
  | none, _ => true

def enough : Nat → Term → Bool
  | 0, _ => false
  | f + 1, t => enoughAt (enough f) (leafOf t) t

/-- The functions in order: each calls only earlier ones, is a rule's, and has a frame past its callers' slots. Every
rule with a function is among them, once; `gen` has steps enough for each. -/
theorem facts : ordered = true ∧ order.Nodup ∧
    order.all (fun i => decide (i < grammar.size) && decide (roots ≤ frameOf i) &&
      (i == commentRule || enough steps (termOf i)) &&
      (callees i).all fun j => decide (frameOf i + need i ≤ frameOf j)) = true ∧
    (List.range grammar.size).all (fun i => !hasFun i || order.contains i) = true := by
  decide +kernel

end DN.News.AbnfOrder
