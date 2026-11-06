import Mathlib

theorem algebra_82770 {b : ℝ} (hb : b > 1) (h : Real.logb 5 (Real.logb 5 b + Real.logb b 125) = 2) :
    Real.logb 5 (b ^ (Real.logb 5 b)) + Real.logb b (125 ^ (Real.logb b 125)) = 619 := by 
  have h1 : Real.logb 5 (Real.logb 5 b + Real.logb b 125) = (2 : ℝ) := h 
  have h15 : Real.logb 5 b + Real.logb b 125 = (25 : ℝ) := by
    have h2 : Real.logb 5 (Real.logb 5 b + Real.logb b 125) = 2 := h 
    rw [Real.logb_eq_iff_rpow_eq] at h2
    · -- Verify $\log_5 b + \log_b 125 = 5^2$.
      nlinarith 
    all_goals 
      try { 
        have h3 : Real.logb 5 b > 0 := by 
          apply Real.logb_pos 
          all_goals linarith 
        have h4 : Real.logb b 125 > 0 := by 
          apply Real.logb_pos 
          all_goals 
            try linarith 
            try norm_num 
        have h5 : Real.logb 5 b + Real.logb b 125 > 0 := by linarith [h3, h4] 
        all_goals nlinarith [h3, h4] 
      }
      try norm_num 
      all_goals 
        nlinarith 
  have h40 : Real.logb 5 b * Real.logb b 125 = (3 : ℝ) := by
    have h41 : Real.logb 5 b = Real.log b / Real.log (5 : ℝ) := by 
      field_simp [Real.logb]
    have h42 : Real.logb b 125 = Real.log (125 : ℝ) / Real.log b := by 
      field_simp [Real.logb]
    have h43 : Real.log (125 : ℝ) = 3 * Real.log (5 : ℝ) := by
      calc
        Real.log (125 : ℝ) = Real.log ((5 : ℝ) ^ 3) := by norm_num 
        _ = 3 * Real.log (5 : ℝ) := by simp [Real.log_pow]
    rw [h41, h42, h43] 
    have hlog5ne : Real.log (5 : ℝ) ≠ 0 := by 
      have h5_pos : (5 : ℝ) > 1 := by norm_num 
      have h7_pos : Real.log (5 : ℝ) > 0 := by 
        apply Real.log_pos 
        all_goals linarith 
      linarith [h7_pos]
    have hlogbne : Real.log b ≠ 0 := by 
      have hb2 : b > 1 := hb 
      have h7_pos : Real.log b > 0 := by 
        apply Real.log_pos 
        all_goals linarith 
      linarith [h7_pos]
    field_simp [hlog5ne, hlogbne]
    <;> ring 
  have h3 : Real.logb 5 (b ^ (Real.logb 5 b)) = (Real.logb 5 b) ^ 2 := by 
    have h4 : Real.logb 5 (b ^ (Real.logb 5 b)) = Real.logb 5 b * Real.logb 5 (b : ℝ) := by 
      rw [Real.logb_rpow_eq_mul_logb_of_pos]
      all_goals linarith 
    have h5 : Real.logb 5 (b : ℝ) = Real.logb 5 b := by simp 
    rw [h4, h5]
    all_goals nlinarith 
  have h4 : Real.logb b (125 ^ (Real.logb b 125)) = (Real.logb b 125) ^ 2 := by 
    have h5 : Real.logb b (125 ^ (Real.logb b 125)) = Real.logb b 125 * Real.logb b (125 : ℝ) := by 
      rw [Real.logb_rpow_eq_mul_logb_of_pos]
      all_goals norm_num 
      all_goals nlinarith 
    have h6 : Real.logb b (125 : ℝ) = Real.logb b 125 := by simp 
    rw [h5, h6]
    all_goals nlinarith 
  calc
    Real.logb 5 (b ^ (Real.logb 5 b)) + Real.logb b (125 ^ (Real.logb b 125))
        = (Real.logb 5 b) ^ 2 + (Real.logb b 125) ^ 2 := by
          rw [h3, h4]
    _ = (619 : ℝ) := by
      have h51 : Real.logb 5 b + Real.logb b 125 = (25 : ℝ) := h15 
      nlinarith [sq_nonneg (Real.logb 5 b - Real.logb b 125), sq_nonneg (Real.logb 5 b + Real.logb b 125), h40, h51]