import Mathlib

theorem number_theory_4756 : ¬(875961 * 2753 ≡ 2410520633[ZMOD 9]) ∧
    ¬(14789 * 23567 ≡ 348532367[ZMOD 9]) ∧
    (24789 * 43717 ≡ 1092700713[ZMOD 9]) := by 
  constructor
  · -- First, prove ¬(875961 * 2753 ≡ 2410520633 [ZMOD 9])
    norm_num [Int.ModEq]
  constructor
  · -- Then prove ¬(14789 * 23567 ≡ 348532367 [ZMOD 9])
    norm_num [Int.ModEq]
  · -- Finally prove (24789 * 43717 ≡ 1092700713 [ZMOD 9])
    norm_num [Int.ModEq]