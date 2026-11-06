import Mathlib

open Real

theorem algebra_183263 {y : ℝ} (hy : y = 10 - 2 * logb 10 32 - 5 * logb 10 25) : y = 0 := by 
  rw [hy]
  have h1 : logb 10 32 = 5 * logb 10 2 := by
    rw [show (32 : ℝ) = 2 ^ 5 by norm_num]
    simp [logb_pow]
  have h2 : logb 10 25 = 2 * logb 10 5 := by
    rw [show (25 : ℝ) = 5 ^ 2 by norm_num]
    simp [logb_pow]
  rw [h1, h2]
  have h3 : logb 10 2 + logb 10 5 = 1 := by
    have h4 : logb 10 2 + logb 10 5 = logb 10 (2 * 5) := by
      rw [logb_mul (by norm_num) (by norm_num)]
    have h5 : logb 10 (2 * 5) = logb 10 10 := by
      norm_num
    have h6 : logb 10 10 = 1 := by
      rw [logb_self_eq_one]
      all_goals norm_num
    linarith
  linarith [h3]