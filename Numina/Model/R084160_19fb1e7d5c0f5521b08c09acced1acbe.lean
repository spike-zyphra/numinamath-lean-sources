import Mathlib

theorem algebra_133238 : √(12^12) = 2^12 * 3^6 := by
  have h1 : (12 ^ 12 : ℝ) = (2^12 * 3^6) ^ 2 := by
    norm_num
  rw [h1]
  rw [Real.sqrt_sq (by norm_num)]
  all_goals norm_num