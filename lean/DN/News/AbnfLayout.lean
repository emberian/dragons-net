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
    aIO ≤ aPow ∧ aIO % 8 = 0 ∧ aInput + inputMax ≤ aIO ∧ aClass ≤ aSets ∧
    aClass + 32 * classes.length ≤ aSets ∧ aTexts + 24 * texts.length ≤ aSets ∧
    (∀ k, k < texts.length → 1 ≤ (texts[k]?.getD ([], false)).1.length ∧
      (texts[k]?.getD ([], false)).1.length ≤ textMax ∧ ∀ b ∈ (texts[k]?.getD ([], false)).1, b < 256) ∧
    aTexts ≠ 0 ∧ aTextBytes ≠ 0 ∧ aPow + 8 * 64 ≤ aMask ∧ aMask + 8 * 8 ≤ aClass ∧
    aClass + 32 * classes.length ≤ aTexts ∧ aTexts + 24 * texts.length ≤ aTextBytes ∧ aTextBytes % 8 = 0 := by
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
theorem input_le : aInput + inputMax ≤ aIO := layout.2.2.2.2.2.2.2.2.2.2.2.1
/-- The masks and the classes lie below the slots. -/
theorem aClass_le : aClass ≤ aSets := layout.2.2.2.2.2.2.2.2.2.2.2.2.1
/-- Stated as the classes' end, not `aTexts`: unfolding that, the kernel would count the classes. -/
theorem classes_end : aClass + 32 * classes.length ≤ aSets := layout.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem texts_end : aTexts + 24 * texts.length ≤ aSets := layout.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
/-- Every string a leaf matches is one byte long at least (`regression_959`)… -/
theorem texts_nonempty : ∀ k, k < texts.length → 1 ≤ (texts[k]?.getD ([], false)).1.length := fun k hk =>
  (layout.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 k hk).1
/-- …and fits `textMax`. -/
theorem texts_short : ∀ k, k < texts.length → (texts[k]?.getD ([], false)).1.length ≤ textMax := fun k hk =>
  (layout.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 k hk).2.1
/-- Every string a leaf matches is of bytes. -/
theorem texts_bytes : ∀ k, k < texts.length → ∀ b ∈ (texts[k]?.getD ([], false)).1, b < 256 := fun k hk =>
  (layout.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 k hk).2.2
/-- The strings' table and bytes are past the area's start: `atOff` adds them. -/
theorem aTexts_ne : aTexts ≠ 0 := layout.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem aTextBytes_ne : aTextBytes ≠ 0 := layout.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
/-- The tables in a row: the powers of two, the masks, the classes, the strings and their bytes. -/
theorem mask_after : aPow + 8 * 64 ≤ aMask := layout.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem class_after : aMask + 8 * 8 ≤ aClass := layout.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem texts_after : aClass + 32 * classes.length ≤ aTexts := layout.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem bytes_after : aTexts + 24 * texts.length ≤ aTextBytes := layout.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem aTextBytes_mod : aTextBytes % 8 = 0 := layout.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end DN.News.AbnfLayout
