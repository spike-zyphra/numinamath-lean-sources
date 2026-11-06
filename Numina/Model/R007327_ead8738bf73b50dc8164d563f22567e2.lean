import Mathlib

theorem algebra_10618 : (7 : ℝ) ^ ((1 : ℝ) / 4) / (7 ^ ((1 : ℝ) / 3)) = 7 ^ ((-1 : ℝ) / 12) := by
  field_simp [← Real.rpow_sub]
  all_goals norm_num
  <;> norm_num
  <;> norm_num