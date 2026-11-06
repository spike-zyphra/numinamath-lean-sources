import Mathlib

open Real

theorem algebra_219114 : logb 10 5 ^ 2 + logb 10 2 * logb 10 50 = 1 := by
  have h1 : logb 10 50 = logb 10 5 + 1 := by
    have h2 : logb 10 50 = logb 10 (5 * 10) := by 
      norm_num
    have h3 : logb 10 (5 * 10) = logb 10 5 + logb 10 10 := by 
      rw [logb_mul (by norm_num) (by norm_num)]
    have h4 : logb 10 10 = 1 := by 
      rw [logb_self_eq_one]
      all_goals norm_num
    rw [h2, h3, h4]
  have h5 : logb 10 2 + logb 10 5 = 1 := by
    have h6 : logb 10 2 + logb 10 5 = logb 10 (2 * 5) := by 
      rw [logb_mul (by norm_num) (by norm_num)]
    have h7 : logb 10 (2 * 5) = logb 10 10 := by 
      norm_num
    have h8 : logb 10 10 = 1 := by 
      rw [logb_self_eq_one]
      all_goals norm_num
    rw [h6, h7, h8]
  have h9 : logb 10 2 = 1 - logb 10 5 := by 
    linarith
  rw [h1, h9]
  nlinarith [h5]