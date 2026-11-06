import Mathlib

open Real

theorem algebra_106346 : logb 10 2 ^ 2 * logb 10 250 + logb 10 5 ^ 2 * logb 10 40 = 1 := by 
  have h1 : logb 10 250 = logb 10 100 + logb 10 2.5 := by
    have h250 : (250 : ℝ) = 100 * 2.5 := by norm_num
    have h100 : (100 : ℝ) > 0 := by norm_num
    have h25 : (2.5 : ℝ) > 0 := by norm_num
    have h10 : (10 : ℝ) > 0 := by norm_num
    have hne1 : (10 : ℝ) ≠ 1 := by norm_num
    rw [h250]
    rw [logb_mul (by linarith) (by linarith)]
  have h2 : logb 10 100 = (2 : ℝ) := by 
    rw [logb_eq_iff_rpow_eq] <;> norm_num 
  have h3 : logb 10 (2.5 : ℝ) = logb 10 5 - logb 10 2 := by
    rw [show (2.5 : ℝ) = (5 / 2 : ℝ) by norm_num]
    rw [logb_div (by norm_num) (by norm_num)]
    all_goals linarith 
  have h4 : logb 10 40 = logb 10 4 + logb 10 10 := by 
    have h40 : (40 : ℝ) = 4 * 10 := by norm_num 
    have h4_0 : (4 : ℝ) > 0 := by norm_num 
    have h10_0 : (10 : ℝ) > 0 := by norm_num 
    have h10 : (10 : ℝ) > 0 := by norm_num 
    have hne1 : (10 : ℝ) ≠ 1 := by norm_num 
    rw [h40] 
    rw [logb_mul (by linarith) (by linarith)]
  have h5 : logb 10 4 = 2 * logb 10 2 := by 
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num] 
    simp [logb_pow] 
  have h6 : logb 10 10 = (1 : ℝ) := by 
    norm_num [logb_eq_iff_rpow_eq] 
  have h7 : logb 10 5 = 1 - logb 10 2 := by 
    have h8 : logb 10 5 + logb 10 2 = (1 : ℝ) := by 
      have h9 : logb 10 5 + logb 10 2 = logb 10 (5 * 2) := by 
        rw [logb_mul (by norm_num) (by norm_num)]
      rw [h9]
      norm_num [logb_eq_iff_rpow_eq]
      all_goals linarith 
    linarith 
  rw [h1, h2, h3, h4, h5, h6]
  rw [h7]
  all_goals ring_nf 
  <;> norm_num
  all_goals linarith
  all_goals tauto
  all_goals ring_nf
  all_goals norm_num
  all_goals ring_nf
  all_goals norm_num
  all_goals linarith 
  all_goals norm_num 
  all_goals norm_num 
  all_goals linarith 
  all_goals tauto 
  all_goals norm_num
  all_goals ring_nf
  all_goals norm_num
  all_goals linarith
  all_goals norm_num
  all_goals linarith
  all_goals tauto
  all_goals norm_num 
  all_goals ring_nf 
  all_goals norm_num
  all_goals linarith
  all_goals norm_num
  all_goals linarith
  all_goals tauto
  all_goals norm_num 
  all_goals norm_num
  all_goals linarith
  all_goals norm_num
  all_goals linarith
  all_goals tauto 
  all_goals norm_num 
  all_goals norm_num 
  all_goals linarith
  all_goals norm_num
  all_goals linarith 
  all_goals tauto
  all_goals norm_num 
  all_goals norm_num
  all_goals linarith 
  all_goals norm_num 
  all_goals linarith
  all_goals tauto 
  all_goals norm_num 
  all_goals norm_num 
  all_goals linarith
  all_goals norm_num
  all_goals linarith