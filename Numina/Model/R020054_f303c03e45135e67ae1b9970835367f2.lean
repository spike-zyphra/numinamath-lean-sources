import Mathlib

open Real

theorem algebra_297514 : (logb 10 2)^3 + (logb 10 5)^3 + 3 * logb 10 2 * logb 10 5 = 1 := by
  have h1 : logb 10 2 + logb 10 5 = 1 := by 
    have h2 : logb 10 2 + logb 10 5 = logb 10 (2 * 5) := by 
      rw [logb_mul (by norm_num) (by norm_num)]
    have h3 : logb 10 (2 * 5) = 1 := by 
      norm_num [logb_eq_iff_rpow_eq]
    linarith [h2, h3]
  have h2 : logb 10 5 = 1 - logb 10 2 := by 
    linarith [h1]
  rw [h2]
  ring