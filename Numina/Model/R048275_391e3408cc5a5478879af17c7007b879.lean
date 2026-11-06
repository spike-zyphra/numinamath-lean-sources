import Mathlib

theorem number_theory_286691 : (4 / 5 : ℝ) < (0.801 : ℝ) ∧ (0.801 : ℝ) < (81 / 100 : ℝ) := by
  constructor
  · norm_num
  · norm_num