import Mathlib

open Real

theorem algebra_187466 : sqrt (25^(1/logb 6 5) + 49^(1/logb 8 7)) = 10 := by
  have h1 : (25 : ℝ) ^ (1 / logb 6 5) = 36 := by
    have h2 : (1 / logb 6 5 : ℝ) = (log 6 / log 5 : ℝ) := by 
      have h3 : logb 6 5 = log 5 / log 6 := by 
        field_simp [logb]
      field_simp [h3]
    
    rw [h2]

    have h4 : (25 : ℝ) ^ (log 6 / log 5 : ℝ) = (5 ^ (2 * (log 6 / log 5 : ℝ)) : ℝ) := by
      rw [show (25 : ℝ) = (5 : ℝ) ^ (2 : ℝ) by norm_num]
      rw [← Real.rpow_mul]
      ring_nf
      all_goals linarith

    rw [h4]

    have h5 : (5 : ℝ) ^ (2 * (log 6 / log 5 : ℝ)) = (( (5 : ℝ) ^ (log 6 / log 5 : ℝ) ) ^ 2 : ℝ) := by
      calc
        (5 : ℝ) ^ (2 * (log 6 / log 5 : ℝ)) = (5 ^ (log 6 / log 5 : ℝ)) ^ 2 := by 
          rw [← Real.rpow_natCast, ← Real.rpow_mul]
          ring_nf
          all_goals linarith
        _ = (( (5 : ℝ) ^ (log 6 / log 5 : ℝ) ) ^ 2 : ℝ) := by 
          norm_num

    rw [h5]

    have h6 : (5 : ℝ) ^ (log 6 / log 5 : ℝ) = (6 : ℝ) := by 
      have h7 : log 6 / log 5 = logb 5 6 := by 
        field_simp [logb]

      rw [h7]
      have h8 : (5 : ℝ) ^ (logb 5 6 : ℝ) = (6 : ℝ) := by 
        rw [Real.rpow_logb]
        all_goals linarith [show 1 < (5 : ℝ) by norm_num, show 1 < (6 : ℝ) by norm_num, show 0 < (5 : ℝ) by norm_num]

      rw [h8]

    rw [h6]
    norm_num

  have h2 : (49 : ℝ) ^ (1 / logb 8 7) = 64 := by 
    have h3 : (1 / logb 8 7 : ℝ) = (log 8 / log 7 : ℝ) := by 
      have h4 : logb 8 7 = log 7 / log 8 := by 
        field_simp [logb]

      field_simp [h4]

    rw [h3]

    have h4 : (49 : ℝ) ^ (log 8 / log 7 : ℝ) = (7 ^ (2 * (log 8 / log 7 : ℝ)) : ℝ) := by
      rw [show (49 : ℝ) = (7 : ℝ) ^ (2 : ℝ) by norm_num]
      rw [← Real.rpow_mul]
      ring_nf
      all_goals linarith

    rw [h4]

    have h5 : (7 : ℝ) ^ (2 * (log 8 / log 7 : ℝ)) = ( ( (7 : ℝ) ^ (log 8 / log 7 : ℝ) ) ^ 2 : ℝ) := by
      calc 
        (7 : ℝ) ^ (2 * (log 8 / log 7 : ℝ)) = (7 ^ (log 8 / log 7 : ℝ)) ^ 2 := by 
          rw [← Real.rpow_natCast, ← Real.rpow_mul]
          ring_nf
          all_goals linarith
        _ = ( ( (7 : ℝ) ^ (log 8 / log 7 : ℝ) ) ^ 2 : ℝ) := by 
          norm_num

    rw [h5]

    have h6 : (7 : ℝ) ^ (log 8 / log 7 : ℝ) = (8 : ℝ) := by 
      have h7 : log 8 / log 7 = logb 7 8 := by 
        field_simp [logb]

      rw [h7]
      have h8 : (7 : ℝ) ^ (logb 7 8 : ℝ) = (8 : ℝ) := by 
        rw [Real.rpow_logb]
        all_goals linarith [show 1 < (7 : ℝ) by norm_num, show 1 < (8 : ℝ) by norm_num, show 0 < (7 : ℝ) by norm_num]

      rw [h8]

    rw [h6]
    norm_num

  have h3 : (25 : ℝ) ^ (1 / logb 6 5) + (49 : ℝ) ^ (1 / logb 8 7) = (100 : ℝ) := by 
    rw [h1, h2]
    norm_num

  rw [h3]
  rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num