import Mathlib

open Real

theorem algebra_190068 : logb 2 2017 / (2 * logb 2 2) < 2 * logb 2 (2017 / 2) := by
  have h1 : logb 2 2 = 1 := by  
    rw [logb_eq_iff_rpow_eq] 
    <;> norm_num
  have h2 : logb 2 (2017 / 2) = logb 2 2017 - logb 2 2 := by
    have hn1 : logb 2 (2017 / 2) = logb 2 2017 - logb 2 2 := by
      rw [Real.logb_div (by norm_num) (by norm_num)]
      all_goals linarith
    linarith [hn1, h1]
  have h3 : logb 2 2017 / (2 * logb 2 2) = (logb 2 2017) / 2 := by
    rw [h1]
    norm_num
  have h4 : 2 * logb 2 (2017 / 2) = 2 * (logb 2 2017 - 1) := by
    rw [h2]
    all_goals 
      rw [h1]
      all_goals nlinarith
  rw [h3, h4]
  have h5 : logb 2 2017 > 0 := by 
    have h51 : logb 2 2017 > 0 := by 
      apply logb_pos
      all_goals norm_num 
    linarith 
  have h7 : logb 2 2017 > 10 := by 
    have h8 : logb 2 2017 > logb 2 1024 := by 
      apply logb_lt_logb
      all_goals norm_num 
    have h9 : logb 2 1024 = 10 := by 
      rw [logb_eq_iff_rpow_eq]
      <;> norm_num 
    linarith 
  nlinarith