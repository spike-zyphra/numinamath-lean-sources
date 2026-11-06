import Mathlib

open Real

theorem inequalities_228653 : sin 1 < logb 3 (sqrt 7) := by
  have h5 : sin 1 < sin (π / 3) := by
    apply sin_lt_sin_of_lt_of_le_pi_div_two
    all_goals linarith [pi_gt_d2, pi_lt_d2]
  have h10 : sin (π / 3) = Real.sqrt 3 / 2 := by
    rw [sin_pi_div_three]
  have h4 : Real.sqrt 3 / 2 < logb 3 (sqrt 7) := by
    have h8 : logb 3 (sqrt 7) = (1 / 2 : ℝ) * logb 3 (7 : ℝ) := by
      have h9 : sqrt 7 = (7 : ℝ) ^ (1 / 2 : ℝ) := by
        rw [Real.sqrt_eq_rpow]
      rw [h9]
      have h10 : logb 3 ((7 : ℝ) ^ (1 / 2 : ℝ)) = (1 / 2 : ℝ) * logb 3 (7 : ℝ) := by
        rw [Real.logb_rpow_eq_mul_logb_of_pos]
        all_goals norm_num
      linarith
    -- Now prove √3 / 2 < (1 / 2) * logb 3 7
    have h11 : Real.sqrt 3 / 2 < (1 / 2 : ℝ) * logb 3 (7 : ℝ) := by 
      have h12 : logb 3 (7 : ℝ) > (7 / 4 : ℝ) := by 
        have h13 : logb 3 (7 : ℝ) > 0 := by
          apply logb_pos
          all_goals norm_num
        -- Now, we need to show that 4 * log(7) > 7 * log(3) implies logb 3 7 > 7 / 4.
        -- First, let me establish the key inequality: 4 * log 7 > 7 * log 3
        have h14 : logb 3 (7 : ℝ) = (log (7 : ℝ) ) / (log (3 : ℝ) ) := by 
          field_simp [logb]
        have h16 : log ( (7 : ℝ) ^ 4 ) > log ( (3 : ℝ) ^ 7 ) := by
          have h17 : (7 : ℝ) ^ 4 = 2401 := by norm_num
          have h18 : (3 : ℝ) ^ 7 = 2187 := by norm_num
          rw [h17, h18]
          apply Real.log_lt_log
          all_goals norm_num
        have h17 : log ( (7 : ℝ) ^ 4 ) = 4 * log (7 : ℝ) := by 
          simp [log_pow]
        have h18 : log ( (3 : ℝ) ^ 7 ) = 7 * log (3 : ℝ) := by 
          simp [log_pow]
        have h19 : 4 * log (7 : ℝ) > 7 * log (3 : ℝ) := by linarith [h16, h17, h18]
        have h20 : log (3 : ℝ) > 0 := by apply log_pos; norm_num 
        have h21 : log (7 : ℝ) / log (3 : ℝ) > (7 / 4 : ℝ) := by 
          apply (lt_div_iff₀' (by linarith [h20])).mpr 
          linarith 
        have h22 : logb 3 (7 : ℝ) > (7 / 4 : ℝ) := by
          rw [h14]
          linarith [h21]
        linarith
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
    nlinarith [h8, h11, Real.sqrt_nonneg 3]
  linarith [h5, h10, h4]