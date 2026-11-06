import Mathlib

theorem algebra_101920 : Real.sqrt (9999^2 + 19999) = 10000 := by 
  have h1 : (9999^2 + 19999 : ℝ) = (10000 : ℝ) ^ 2 := by
    norm_num
  rw [h1]
  rw [Real.sqrt_sq]
  all_goals norm_num