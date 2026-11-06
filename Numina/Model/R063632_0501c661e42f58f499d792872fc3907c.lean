import Mathlib

theorem algebra_20275 : Real.sqrt (5*10*14*21*15*20) = 2100 := by
  have h1 : (5 : ℝ) * 10 * 14 * 21 * 15 * 20 = (2100 : ℝ) ^ 2 := by norm_num
  rw [h1]
  rw [Real.sqrt_sq (by norm_num)]
  all_goals norm_num