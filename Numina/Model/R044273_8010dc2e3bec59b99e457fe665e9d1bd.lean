import Mathlib

theorem algebra_283560 :
    {x : ℝ | Real.sqrt (0.12 ^ (0.12 * x) + 5) + Real.sqrt (0.12 ^ (0.12 * x) + 6) = 5} =
    {x : ℝ | x = Real.log (0.76) / (0.12 * Real.log 0.12)} := by 
  ext x 
  simp only [Set.mem_setOf_eq]
  constructor 
  · -- Assume the equation holds, prove the value 
    intro h 
    have h3 : Real.sqrt (0.12 ^ (0.12 * x) + 5) + Real.sqrt (0.12 ^ (0.12 * x) + 6) = 5 := h
    have h4 : 0 ≤ (0.12 ^ (0.12 * x) + 5 : ℝ) := by
      have h5 : 0 ≤ (0.12 ^ (0.12 * x) : ℝ) := by positivity
      linarith 
    have h6 : 0 ≤ (0.12 ^ (0.12 * x) + 6 : ℝ) := by 
      have h5 : 0 ≤ (0.12 ^ (0.12 * x) : ℝ) := by positivity 
      linarith
    have h7 : (Real.sqrt (0.12 ^ (0.12 * x) + 5) + Real.sqrt (0.12 ^ (0.12 * x) + 6)) ^ 2 = (5 : ℝ) ^ 2 := by 
      rw [h3]
    have h8 : (Real.sqrt (0.12 ^ (0.12 * x) + 5)) ^ 2 + (Real.sqrt (0.12 ^ (0.12 * x) + 6)) ^ 2 + 2 * (Real.sqrt (0.12 ^ (0.12 * x) + 5) * Real.sqrt (0.12 ^ (0.12 * x) + 6)) = 25 := by 
      nlinarith [h7] 
    have h9 : (Real.sqrt (0.12 ^ (0.12 * x) + 5)) ^ 2 = 0.12 ^ (0.12 * x) + 5 := Real.sq_sqrt (show 0 ≤ (0.12 ^ (0.12 * x) + 5 : ℝ) by positivity)
    have h10 : (Real.sqrt (0.12 ^ (0.12 * x) + 6)) ^ 2 = 0.12 ^ (0.12 * x) + 6 := Real.sq_sqrt (show 0 ≤ (0.12 ^ (0.12 * x) + 6 : ℝ) by positivity)
    have h11 : Real.sqrt (0.12 ^ (0.12 * x) + 5) * Real.sqrt (0.12 ^ (0.12 * x) + 6) = (7 - (0.12 ^ (0.12 * x)) : ℝ) := by
      nlinarith [h8, h9, h10, Real.sqrt_nonneg (0.12 ^ (0.12 * x) + 5), Real.sqrt_nonneg (0.12 ^ (0.12 * x) + 6)]
    have h12 : (0.12 ^ (0.12 * x)) = (0.76 : ℝ) := by 
      have h13 : (Real.sqrt (0.12 ^ (0.12 * x) + 5) * Real.sqrt (0.12 ^ (0.12 * x) + 6)) ^ 2 = (7 - (0.12 ^ (0.12 * x)) : ℝ) ^ 2 := by 
        rw [h11]
      nlinarith [Real.sqrt_nonneg (0.12 ^ (0.12 * x) + 5), Real.sqrt_nonneg (0.12 ^ (0.12 * x) + 6), h9, h10, Real.sqrt_nonneg (0.12 ^ (0.12 * x) + 5), Real.sqrt_nonneg (0.12 ^ (0.12 * x) + 6), Real.rpow_pos_of_pos (show (0.12 : ℝ) > 0 by norm_num) (0.12 * x)]
    have h14 : x = Real.log (0.76) / (0.12 * Real.log 0.12) := by
      have h16 : (0.12 : ℝ) ^ (0.12 * x) = (0.76 : ℝ) := h12
      have h17 : 0.12 * x = Real.log (0.76) / Real.log (0.12 : ℝ) := by 
        have h18 : Real.log ((0.12 : ℝ) ^ (0.12 * x)) = Real.log (0.76 : ℝ) := by 
          rw [h16]
        have h19 : Real.log ((0.12 : ℝ) ^ (0.12 * x)) = (0.12 * x) * Real.log (0.12 : ℝ) := by 
          rw [Real.log_rpow]
          all_goals norm_num
        have h20 : Real.log (0.12 : ℝ) ≠ 0 := by 
          have h21 : Real.log (0.12 : ℝ) < 0 := by 
            have h22 : Real.log (0.12 : ℝ) < Real.log (1 : ℝ) := Real.log_lt_log (by norm_num) (by norm_num)
            have h23 : Real.log (1 : ℝ) = 0 := Real.log_one 
            linarith 
          linarith 
        have eq1 : (0.12 * x) * Real.log (0.12 : ℝ) = Real.log (0.76 : ℝ) := by 
          linarith [h18, h19]
        have eq2 : (0.12 * x) = Real.log (0.76 : ℝ) / Real.log (0.12 : ℝ) := by 
          field_simp [h20] at eq1 ⊢
          nlinarith 
        linarith 
      have h28 : Real.log (0.12 : ℝ) ≠ 0 := by 
        have h21 : Real.log (0.12 : ℝ) < 0 := by 
          have h22 : Real.log (0.12 : ℝ) < Real.log (1 : ℝ) := Real.log_lt_log (by norm_num) (by norm_num)
          have h23 : Real.log (1 : ℝ) = 0 := Real.log_one 
          linarith 
        linarith 
      field_simp [h28] at h17 ⊢ 
      linarith 
    linarith 
  · -- Assume the value, prove the equation 
    intro h_eq 
    rw [show x = Real.log (0.76) / (0.12 * Real.log 0.12) by linarith [h_eq] ]
    have h_eq1 : (0.12 : ℝ) ^ (0.12 * (Real.log (0.76) / (0.12 * Real.log 0.12) ) ) = (0.76 : ℝ) := by
      have h17 : 0.12 * (Real.log (0.76) / (0.12 * Real.log 0.12)) = Real.log (0.76) / Real.log (0.12 : ℝ) := by 
        field_simp
        <;> ring 
      rw [h17] 
      have h18 : Real.log (0.12 : ℝ) ≠ 0 := by 
        have h21 : Real.log (0.12 : ℝ) < 0 := by 
          have h22 : Real.log (0.12 : ℝ) < Real.log (1 : ℝ) := Real.log_lt_log (by norm_num) (by norm_num)
          have h23 : Real.log (1 : ℝ) = 0 := Real.log_one 
          linarith 
        linarith 
      have h19 : (0.12 : ℝ) ^ (Real.log (0.76) / Real.log (0.12 : ℝ) ) = (0.76 : ℝ) := by 
        have h20 : Real.log (0.76) / Real.log (0.12 : ℝ) = Real.logb (0.12 : ℝ) (0.76 : ℝ) := by 
          field_simp [Real.logb] 
        rw [h20]
        rw [Real.rpow_logb]
        all_goals norm_num 
      linarith 
    have h_eq2 : Real.sqrt ((0.12 : ℝ) ^ (0.12 * (Real.log (0.76) / (0.12 * Real.log 0.12)) ) + 5) + Real.sqrt ((0.12 : ℝ) ^ (0.12 * (Real.log (0.76) / (0.12 * Real.log 0.12)) ) + 6) = 5 := by
      have h12 : (0.12 : ℝ) ^ (0.12 * (Real.log (0.76) / (0.12 * Real.log 0.12)) ) = (0.76 : ℝ) := h_eq1 
      rw [h12] 
      have h3 : Real.sqrt (0.76 + 5) = (2.4 : ℝ) := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
      have h4 : Real.sqrt (0.76 + 6) = (2.6 : ℝ) := by 
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
      rw [h3, h4] 
      norm_num 
    linarith