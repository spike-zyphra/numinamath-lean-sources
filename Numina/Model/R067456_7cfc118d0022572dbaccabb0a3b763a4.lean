import Mathlib

theorem number_theory_233021 : (59 : ℤ) % 3 = 2 ∧ (59 : ℤ) % 4 = 3 ∧ (59 : ℤ) % 5 = 4 := by
  constructor
  · norm_num
  constructor
  · norm_num
  · norm_num