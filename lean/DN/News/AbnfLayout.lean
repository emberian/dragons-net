-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.AbnfProg

/-!
# DN.News.AbnfLayout

The grammar area's sizes, worked out once by the kernel (`layout`). The kernel works a closed number such as
`aSets` or `slots` out wherever it unfolds one, which takes seconds, so proofs use these bounds and leave the
numbers folded: `aSets + slots * setSize` is `size` by its definition.
-/

namespace DN.News.AbnfLayout

open DN.News.AbnfProg

/-- The slots, the tables and the strings' bytes: where they lie and how many there are; what the host writes, the
header, the starts and the input, below `aIO`, and the tables from there. -/
theorem layout : 2 ≤ slots ∧ slots ≤ 256 ∧ aSets ≤ 2 ^ 20 ∧ aSets % 8 = 0 ∧ aPow + 8 * 64 ≤ aSets ∧
    aTexts % 8 = 0 ∧ classes.length ≤ 256 ∧ texts.length ≤ 256 ∧ aTextBytes + textBytes + textMax + 1 ≤ aSets ∧
    aIO ≤ aPow ∧ aIO % 8 = 0 ∧ aInput + inputMax ≤ aIO := by
  decide +kernel

theorem slots_two : 2 ≤ slots := layout.1
theorem slots_le : slots ≤ 256 := layout.2.1
theorem aSets_le : aSets ≤ 2 ^ 20 := layout.2.2.1
theorem aSets_mod : aSets % 8 = 0 := layout.2.2.2.1
theorem pow_lt : aPow + 8 * 64 ≤ aSets := layout.2.2.2.2.1
theorem aTexts_mod : aTexts % 8 = 0 := layout.2.2.2.2.2.1
theorem classes_le : classes.length ≤ 256 := layout.2.2.2.2.2.2.1
theorem texts_le : texts.length ≤ 256 := layout.2.2.2.2.2.2.2.1
theorem textBytes_le : aTextBytes + textBytes + textMax + 1 ≤ aSets := layout.2.2.2.2.2.2.2.2.1
/-- The host's span ends where the tables start. -/
theorem io_le : aIO ≤ aPow := layout.2.2.2.2.2.2.2.2.2.1
theorem io_mod : aIO % 8 = 0 := layout.2.2.2.2.2.2.2.2.2.2.1
/-- The longest input fits in the host's span. -/
theorem input_le : aInput + inputMax ≤ aIO := layout.2.2.2.2.2.2.2.2.2.2.2

end DN.News.AbnfLayout
