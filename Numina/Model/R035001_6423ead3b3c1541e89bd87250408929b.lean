import Mathlib

open Real

theorem algebra_269303 : sqrt (25^(1/(logb 6 5)) + 49^(1/(logb 8 7))) = 10 := by
  have h1 : (25 : ℝ) ^ (1 / (logb 6 5)) = 36 := by
    have h2 : logb 6 5 = (log 5) / (log 6) := by 
      field_simp [logb]
    rw [h2]
    have h3 : (25 : ℝ) ^ (1 / ((log 5) / (log 6))) = (5 ^ (2 : ℝ) ) ^ (log 6 / log 5 : ℝ) := by
      have h5 : (1 / ((log 5) / (log 6))) = (log 6 / log 5) := by 
        field_simp 
      rw [h5]
      have h5 : (25 : ℝ) = (5 : ℝ) ^ (2 : ℝ) := by norm_num
      rw [h5]
    have h4 : (5 ^ (2 : ℝ) : ℝ) ^ (log 6 / log 5 : ℝ) = (5 : ℝ) ^ (2 * (log 6 / log 5) : ℝ) := by 
      rw [← Real.rpow_mul]
      ring 
      all_goals positivity 
    have h5 : (5 : ℝ) ^ (2 * (log 6 / log 5) : ℝ) = ((5 : ℝ) ^ (log 6 / log 5 : ℝ)) ^ 2 := by 
      calc 
        (5 : ℝ) ^ (2 * (log 6 / log 5) : ℝ) = ((5 : ℝ) ^ (log 6 / log 5 : ℝ)) ^ (2 : ℝ) := by 
          rw [← Real.rpow_mul]
          ring
          all_goals positivity 
        _ = ((5 : ℝ) ^ (log 6 / log 5 : ℝ)) ^ 2 := by 
          norm_cast 
    have h6 : (5 : ℝ) ^ (log 6 / log 5 : ℝ) = 6 := by 
      have h7 : log 6 / log 5 = (logb 5 6 : ℝ) := by 
        field_simp [logb]
      rw [h7]
      have h8 : (5 : ℝ) ^ (logb 5 6 : ℝ) = (6 : ℝ) := by 
        rw [Real.rpow_logb]
        all_goals norm_num 
      linarith
    rw [h3, h4, h5, h6]
    all_goals norm_num
  have h2 : (49 : ℝ) ^ (1 / (logb 8 7)) = 64 := by
    have h21 : logb 8 7 = (log 7) / (log 8) := by 
      field_simp [logb]
    rw [h21]
    have h3 : (49 : ℝ) ^ (1 / ((log 7) / (log 8))) = (7 ^ (2 : ℝ) ) ^ (log 8 / log 7 : ℝ) := by
      have h5 : (1 / ((log 7) / (log 8))) = (log 8 / log 7) := by 
        field_simp 
      rw [h5]
      have h5 : (49 : ℝ) = (7 : ℝ) ^ (2 : ℝ) := by norm_num
      rw [h5]
    have h4 : (7 ^ (2 : ℝ) : ℝ) ^ (log 8 / log 7 : ℝ) = (7 : ℝ) ^ (2 * (log 8 / log 7) : ℝ) := by 
      rw [← Real.rpow_mul]
      ring 
      all_goals positivity 
    have h5 : (7 : ℝ) ^ (2 * (log 8 / log 7) : ℝ) = ((7 : ℝ) ^ (log 8 / log 7 : ℝ)) ^ 2 := by 
      calc 
        (7 : ℝ) ^ (2 * (log 8 / log 7) : ℝ) = ((7 : ℝ) ^ (log 8 / log 7 : ℝ)) ^ (2 : ℝ) := by 
          rw [← Real.rpow_mul]
          ring 
          all_goals positivity 
        _ = ((7 : ℝ) ^ (log 8 / log 7 : ℝ)) ^ 2 := by 
          norm_cast 
    have h6 : (7 : ℝ) ^ (log 8 / log 7 : ℝ) = 8 := by 
      have h71 : log 8 / log 7 = logb 7 8 := by 
        field_simp [logb]
      rw [h71]
      have h8 : (7 : ℝ) ^ (logb 7 8 : ℝ) = (8 : ℝ) := by 
        rw [Real.rpow_logb]
        all_goals norm_num 
      linarith 
    rw [h3, h4, h5, h6]
    all_goals norm_num 
  rw [h1, h2]
  rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num