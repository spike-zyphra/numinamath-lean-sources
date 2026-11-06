import Mathlib

open Real

theorem inequalities_49544 : 1 / logb 2 π + 1 / logb 5 π > 2 := by

  have h1 : 1 / logb 2 π + 1 / logb 5 π = (log 10) / (log π) := by 
    have h2 : logb 2 π = (log π) / (log 2) := by
      field_simp [logb]
    have h3 : logb 5 π = (log π) / (log 5) := by
      field_simp [logb]
    rw [h2, h3]
    have h4 : 1 / ((log π) / (log 2)) + 1 / ((log π) / (log 5)) = (log 2) / (log π) + (log 5) / (log π) := by 
      field_simp
      all_goals ring
    rw [h4]
    have h5 : (log 2) / (log π) + (log 5) / (log π) = (log 2 + log 5) / (log π) := by 
      ring_nf
    rw [h5]
    have h6 : log 2 + log 5 = log 10 := by 
      calc
        log 2 + log 5 = log (2 * 5) := by rw [log_mul (by norm_num) (by norm_num)]
        _ = log 10 := by norm_num
    rw [h6]
  
  rw [h1]

  have h2 : log π > 0 := by 
    apply log_pos
    linarith [Real.pi_gt_31415, Real.pi_lt_31416]

  have h3 : log 10 > 2 * log π := by
    have h4 : (10 : ℝ) > Real.pi ^ 2 := by
      nlinarith [Real.pi_lt_31416, Real.pi_gt_31415]
    have h6 : log 10 > log (Real.pi ^ 2) := by 
      apply Real.log_lt_log
      all_goals nlinarith [Real.pi_lt_31416, Real.pi_gt_31415, h4]
    have h7 : log (Real.pi ^ 2) = 2 * log Real.pi := by 
      simp [log_pow]
    linarith [h6, h7]

  have h4 : (log 10) / (log π) > 2 := by 
    have h16 : log π > 0 := h2
    have h15 : log 10 > 2 * log π := h3
    have h17 : (log 10) / (log π) > (2 * log π) / (log π) := by
      apply (div_lt_div_right h16).mpr
      linarith
    have h18 : (2 * log π) / (log π) = 2 := by 
      have h0 : log π > 0 := h16
      field_simp [h0]
      all_goals nlinarith
    linarith [h17, h18]

  linarith [h4]