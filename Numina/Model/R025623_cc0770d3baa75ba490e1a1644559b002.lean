import Mathlib

open Real

theorem inequalities_164041 {x y : ℝ} (h : (logb 2 3)^x - (logb 5 3)^x ≥ (logb 2 3)^(-y) - (logb 5 3)^(-y)) :
    x + y ≥ 0 := by 
  have h1 : logb 2 3 > 1 := by 
    have h2 : logb 2 3 > logb 2 2 := by
      apply Real.logb_lt_logb
      all_goals norm_num
    have h3 : logb 2 2 = 1 := by 
      rw [Real.logb_self_eq_one]
      all_goals norm_num
    linarith [h2, h3]

  have h2 : logb 5 3 > 0 := by 
    apply Real.logb_pos
    all_goals norm_num

  have h3 : logb 5 3 < 1 := by 
    have h4 : logb 5 3 < logb 5 5 := by
      apply Real.logb_lt_logb
      all_goals norm_num
    have h5 : logb 5 5 = 1 := by 
      rw [Real.logb_eq_iff_rpow_eq] <;> (norm_num)
    nlinarith [h4, h5]

  by_contra h4
  push_neg at h4

  have h4' : x < -y := by linarith

  have h5 : (logb 2 3 : ℝ) ^ x < (logb 2 3 : ℝ) ^ (-y : ℝ) := by
    apply Real.rpow_lt_rpow_of_exponent_lt
    all_goals
      linarith [h1, h4']

  have h6 : (logb 5 3 : ℝ) ^ x > (logb 5 3 : ℝ) ^ (-y : ℝ) := by
    apply Real.rpow_lt_rpow_of_exponent_gt
    all_goals
      linarith [h2, h3, h4']

  have h8 : (logb 2 3 : ℝ) ^ x - (logb 5 3 : ℝ) ^ x < (logb 2 3 : ℝ) ^ (-y : ℝ) - (logb 5 3 : ℝ) ^ (-y : ℝ) := by 
    linarith [h5, h6]

  linarith [h, h8]