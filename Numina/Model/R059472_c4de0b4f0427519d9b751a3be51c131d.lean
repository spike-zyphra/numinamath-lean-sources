import Mathlib

theorem algebra_290756 : ∃ n : ℤ, n = Real.sqrt (((119^2 - 17^2) / (119 - 17)) - 10^2) := by
  use 6
  have h1 : ((119^2 - 17^2) / (119 - 17) : ℝ) - (10^2 : ℝ) = (36 : ℝ) := by norm_num
  rw [h1]
  have h2 : Real.sqrt (36 : ℝ) = (6 : ℝ) := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  norm_num [h2]
  all_goals norm_num
  all_goals norm_num [h2]