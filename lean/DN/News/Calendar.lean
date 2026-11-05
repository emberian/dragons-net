-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.ArticleSpec

/-!
# DN.News.Calendar

The day of the calendar packed in one word as `artCivilOf` gives it back (`civilWord`), and the bound that keeps its
steps from going below zero (`cal_doe`).
-/

namespace DN.News.Calendar

/-- A day of the Gregorian calendar as `artCivilOf` gives it back: its year, month and day in one word. -/
def civilWord (z : Nat) : Nat :=
  (ArticleSpec.civilFromDays z).1 * 512 + (ArticleSpec.civilFromDays z).2.1 * 32 + (ArticleSpec.civilFromDays z).2.2

/-- The day of the year never falls below the year's start: no step of `artCivilOf` goes below zero. -/
theorem cal_doe (doe : Nat) (h : doe < 146097) :
    365 * ((doe - doe / 1460 + doe / 36524 - doe / 146096) / 365) +
      (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365 / 4 -
      (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365 / 100 ≤ doe := by
  generalize ha1 : doe / 1460 = a1
  generalize ha2 : doe / 36524 = a2
  generalize ha3 : doe / 146096 = a3
  have e1 : 1460 * a1 ≤ doe ∧ doe < 1460 * a1 + 1460 := by omega
  have e2 : 36524 * a2 ≤ doe ∧ doe < 36524 * a2 + 36524 := by omega
  have e3 : 146096 * a3 ≤ doe ∧ doe < 146096 * a3 + 146096 := by omega
  have h21 : a2 ≤ a1 := by omega
  generalize hy : (doe - a1 + a2 - a3) / 365 = y
  have ey : 365 * y ≤ doe - a1 + a2 - a3 ∧ doe - a1 + a2 - a3 < 365 * y + 365 := by omega
  have i1 : y / 4 ≤ a1 := by omega
  have i2 : a2 - a3 ≤ y / 100 := by
    rcases (show a2 = 0 ∨ a2 = 1 ∨ a2 = 2 ∨ a2 = 3 ∨ a2 = 4 by omega) with h2 | h2 | h2 | h2 | h2 <;>
      subst h2 <;> omega
  omega

end DN.News.Calendar
