import Mathlib

theorem other_202483 :
    70 = 7 * 10 ∧ 100 = 10 * 10 ∧ 80 = 8 * 10 ∧
    9 = 90 / 10 ∧ 5 = 50 / 10 ∧ 1 = 10 / 10 := by
  constructor
  · norm_num  -- Proves 70 = 7 * 10
  constructor
  · norm_num  -- Proves 100 = 10 * 10
  constructor
  · norm_num  -- Proves 80 = 8 * 10
  constructor
  · norm_num  -- Proves 9 = 90 / 10
  constructor
  · norm_num  -- Proves 5 = 50 / 10
  · norm_num  -- Proves 1 = 10 / 10