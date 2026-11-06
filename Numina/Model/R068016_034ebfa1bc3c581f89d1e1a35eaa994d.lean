import Mathlib

open Real

theorem algebra_163469 :
    (logb 2 3)^3 - (logb 2 6)^3 - (logb 2 12)^3 + (logb 2 24)^3 = 6 * logb 2 72 := by 
  have h2 : logb 2 6 = 1 + logb 2 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num]
    rw [logb_mul (by norm_num) (by norm_num)]
    have h3 : logb 2 (2 : ℝ) = 1 := by 
      rw [logb_self_eq_one]
      all_goals norm_num
    rw [h3]
    all_goals ring

  have h4 : logb 2 12 = 2 + logb 2 3 := by
    rw [show (12 : ℝ) = 2 ^ 2 * 3 by norm_num]
    rw [logb_mul (by norm_num) (by norm_num)]
    simp [logb_pow]
    all_goals ring

  have h5 : logb 2 24 = 3 + logb 2 3 := by 
    rw [show (24 : ℝ) = 2 ^ 3 * 3 by norm_num]
    rw [logb_mul (by norm_num) (by norm_num)]
    simp [logb_pow]
    all_goals ring

  have h6 : logb 2 72 = 3 + 2 * logb 2 3 := by 
    rw [show (72 : ℝ) = 2 ^ 3 * 3 ^ 2 by norm_num]
    rw [logb_mul (by norm_num) (by norm_num)]
    simp [logb_pow]
    all_goals ring
  
  rw [h2, h4, h5, h6]
  nlinarith [sq_nonneg (logb 2 3 - 1), sq_nonneg (logb 2 3 - 2), sq_nonneg (logb 2 3 - 3)]