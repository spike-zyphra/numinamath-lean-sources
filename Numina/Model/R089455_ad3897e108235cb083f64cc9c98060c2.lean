import Mathlib

theorem number_theory_93848 : (19 / 15 : ℚ) < (17 / 13 : ℚ) ∧ (17 / 13 : ℚ) < (15 / 11 : ℚ) := by
  constructor
  · norm_num
  · norm_num