import Mathlib

theorem algebra_175656 : ((Real.sqrt 2 + 1)^7 + (Real.sqrt 2 - 1)^7)^2 -
    ((Real.sqrt 2 + 1)^7 - (Real.sqrt 2 - 1)^7)^2 = 4 := by 
  have h1 : ((Real.sqrt 2 + 1) ^ 7 + (Real.sqrt 2 - 1) ^ 7) ^ 2 - ((Real.sqrt 2 + 1) ^ 7 - (Real.sqrt 2 - 1) ^ 7) ^ 2 = 4 * ((Real.sqrt 2 + 1) ^ 7 * (Real.sqrt 2 - 1) ^ 7) := by 
    ring
  have h2 : (Real.sqrt 2 + 1) * (Real.sqrt 2 - 1) = 1 := by
    calc 
      (Real.sqrt 2 + 1) * (Real.sqrt 2 - 1) = (Real.sqrt 2)^2 - 1^2 := by ring
      _ = (Real.sqrt 2)^2 - 1 := by norm_num
      _ = (2 : ℝ) - 1 := by rw [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      _ = (1 : ℝ) := by norm_num
  have h3 : (Real.sqrt 2 + 1) ^ 7 * (Real.sqrt 2 - 1) ^ 7 = 1 := by
    calc 
      (Real.sqrt 2 + 1) ^ 7 * (Real.sqrt 2 - 1) ^ 7 = ((Real.sqrt 2 + 1) * (Real.sqrt 2 - 1)) ^ 7 := by ring
      _ = (1 : ℝ) ^ 7 := by rw [h2]
      _ = (1 : ℝ) := by norm_num 
  rw [h1, h3]
  all_goals norm_num