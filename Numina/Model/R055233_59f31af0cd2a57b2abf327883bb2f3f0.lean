import Mathlib

theorem algebra_251405 : (3 : ℝ) ^ (Real.sqrt (Real.logb 2 3)) > (2 : ℝ) ^ (Real.sqrt (Real.logb 3 2)) := by 
  have h1 : Real.logb 2 3 > 0 := by 
    apply Real.logb_pos 
    all_goals norm_num
  have h2 : Real.logb 3 2 > 0 := by 
    apply Real.logb_pos 
    all_goals norm_num
  have h4 : Real.sqrt (Real.logb 2 3) > 1 := by
    have h5 : Real.logb 2 3 > 1 := by 
      have h6 : Real.logb 2 3 > Real.logb 2 2 := by
        apply Real.logb_lt_logb 
        all_goals norm_num 
      have h7 : Real.logb 2 2 = 1 := by 
        rw [Real.logb_self_eq_one] 
        all_goals norm_num 
      linarith [h7, h6]
    have h8 : Real.sqrt (Real.logb 2 3) > Real.sqrt (1 : ℝ) := by 
      apply Real.sqrt_lt_sqrt 
      all_goals linarith [h5, show (0 : ℝ) < (1 : ℝ) by norm_num]
    have h9 : Real.sqrt (1 : ℝ) = 1 := Real.sqrt_one
    linarith [h8, h9]
  have h10 : Real.sqrt (Real.logb 3 2) < 1 := by
    have h11 : Real.logb 3 2 < 1 := by 
      have h12 : Real.logb 3 2 < Real.logb 3 3 := by 
        apply Real.logb_lt_logb 
        all_goals norm_num 
      have h13 : Real.logb 3 3 = 1 := by 
        rw [Real.logb_self_eq_one] 
        all_goals norm_num 
      linarith [h13, h12]
    have h14 : Real.sqrt (Real.logb 3 2) < Real.sqrt (1 : ℝ) := by 
      apply Real.sqrt_lt_sqrt 
      all_goals linarith [h11, show (0 : ℝ) < (1 : ℝ) by norm_num]
    have h15 : Real.sqrt (1 : ℝ) = 1 := Real.sqrt_one
    linarith [h14, h15]
  have h16 : (3 : ℝ) ^ (Real.sqrt (Real.logb 2 3)) > 3 := by 
    have h17 : Real.sqrt (Real.logb 2 3) > (1 : ℝ) := h4
    have h18 : (3 : ℝ) ^ (Real.sqrt (Real.logb 2 3)) > (3 : ℝ) ^ (1 : ℝ) := by 
      apply Real.rpow_lt_rpow_of_exponent_lt 
      all_goals linarith 
    have h19 : (3 : ℝ) ^ (1 : ℝ) = (3 : ℝ) := by 
      simp 
    linarith [h18, h19]
  have h20 : (2 : ℝ) ^ (Real.sqrt (Real.logb 3 2)) < (2 : ℝ) := by 
    have h21 : Real.sqrt (Real.logb 3 2) < (1 : ℝ) := h10
    have h22 : (2 : ℝ) ^ (Real.sqrt (Real.logb 3 2)) < (2 : ℝ) ^ (1 : ℝ) := by 
      apply Real.rpow_lt_rpow_of_exponent_lt 
      all_goals linarith 
    have h23 : (2 : ℝ) ^ (1 : ℝ) = (2 : ℝ) := by 
      simp 
    linarith [h22, h23]
  linarith [h16, h20]