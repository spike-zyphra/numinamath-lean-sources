import Mathlib

open Real

theorem inequalities_208322 : logb 3 4 > logb 4 5 := by 
  have h1 : logb 3 4 = (log 4) / (log 3) := by 
    field_simp [logb]
    all_goals linarith 
  have h2 : logb 4 5 = (log 5) / (log 4) := by 
    field_simp [logb]
    all_goals linarith 
  rw [h1, h2]
  have h3 : log 3 > 0 := by
    apply log_pos 
    all_goals linarith 
  have h4 : log 4 > 0 := by 
    apply log_pos 
    all_goals linarith 
  have h5 : log 4 > log 3 := by 
    have h1 : log 4 > log 3 := by 
      apply Real.log_lt_log 
      all_goals linarith 
    linarith 
  have h6 : log 5 > log 4 := by 
    have h2 : log 5 > log 4 := by 
      apply Real.log_lt_log 
      all_goals linarith 
    linarith 
  have h7 : (log 4) ^ 2 > (log 3) * (log 5) := by 
    have h8 : log (16 : ℝ) = 2 * log 4 := by 
      calc 
        log (16 : ℝ) = log ((4 : ℝ) ^ 2) := by norm_num 
        _ = 2 * log (4 : ℝ) := by simp [log_pow]
    have h9 : log (15 : ℝ) = log 3 + log 5 := by 
      calc 
        log (15 : ℝ) = log ((3 : ℝ) * (5 : ℝ)) := by norm_num 
        _ = log (3 : ℝ) + log (5 : ℝ) := by rw [log_mul (by linarith) (by linarith)]
    have h10 : log (16 : ℝ) > log (15 : ℝ) := by 
      apply Real.log_lt_log 
      all_goals linarith 
    have h11 : 2 * log 4 > log 3 + log 5 := by 
      linarith [h8, h9, h10] 
    nlinarith [Real.log_pos (show (4 : ℝ) > 1 by norm_num : (4 : ℝ) > 1), Real.log_pos (show (5 : ℝ) > 1 by norm_num : (5 : ℝ) > 1), Real.log_pos (show (3 : ℝ) > 1 by norm_num : (3 : ℝ) > 1),
      mul_pos (show 0 < (4 : ℝ) - (3 : ℝ) by linarith) (show 0 < (5 : ℝ) - (4 : ℝ) by linarith),
      h11]
  have h8 : (log 4) / (log 3) > (log 5) / (log 4) := by 
    apply (div_lt_div_iff (by positivity) (by positivity)).mpr 
    nlinarith [Real.log_pos (show (4 : ℝ) > 1 by norm_num : (4 : ℝ) > 1), Real.log_pos (show (5 : ℝ) > 1 by norm_num : (5 : ℝ) > 1), Real.log_pos (show (3 : ℝ) > 1 by norm_num : (3 : ℝ) > 1)]
  linarith [h8]