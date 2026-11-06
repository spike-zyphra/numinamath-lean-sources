import Mathlib

open Real

theorem algebra_16300 : logb 10 4 + 2 * logb 10 5 + 3 * logb 10 2 + 6 * logb 10 5 + logb 10 8 = 8 := by 
  have eq1 : logb 10 4 = 2 * logb 10 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
    simp [logb_pow]
  have eq2 : logb 10 8 = 3 * logb 10 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num]
    simp [logb_pow]
  have h4 : logb 10 2 + logb 10 5 = 1 := by
    have h5 : logb 10 2 + logb 10 5 = logb 10 (2 * 5) := by
      rw [logb_mul (by norm_num) (by norm_num)]
    rw [h5]
    norm_num [logb_self_eq_one]
  calc 
    logb 10 4 + 2 * logb 10 5 + 3 * logb 10 2 + 6 * logb 10 5 + logb 10 8 
        = (2 * logb 10 2) + 2 * logb 10 5 + 3 * logb 10 2 + 6 * logb 10 5 + (3 * logb 10 2) := by 
          rw [eq1, eq2]
          all_goals norm_num
    _ = (2 + 3 + 3) * logb 10 2 + (2 + 6) * logb 10 5 := by 
      ring
    _ = 8 * (logb 10 2 + logb 10 5) := by 
      ring
    _ = 8 * 1 := by 
      rw [h4]
    _ = 8 := by 
      norm_num