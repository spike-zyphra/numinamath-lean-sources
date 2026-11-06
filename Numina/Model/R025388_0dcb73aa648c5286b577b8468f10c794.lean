import Mathlib

open Real

theorem algebra_247967 : 1 / (1 - logb 2 20) + 1 / (1 - logb 5 50) = -1 := by 
  have h1 : logb 2 20 = log 20 / log 2 := by 
    field_simp [logb]
  have h2 : logb 5 50 = log 50 / log 5 := by 
    field_simp [logb]
  rw [h1, h2]
  have h3 : log 20 = 2 * log 2 + log 5 := by 
    calc 
      log 20 = log (2^2 * 5) := by norm_num 
      _ = log (2^2) + log 5 := by rw [log_mul (by norm_num) (by norm_num)]
      _ = 2 * log 2 + log 5 := by simp [log_pow]
  have h4 : log 50 = log 2 + 2 * log 5 := by 
    calc 
      log 50 = log (2 * 5^2) := by norm_num 
      _ = log 2 + log (5^2) := by rw [log_mul (by norm_num) (by norm_num)]
      _ = log 2 + 2 * log 5 := by simp [log_pow]
  rw [h3, h4] at *
  have h6 : 1 - (2 * log 2 + log 5) / log 2 = - (log 2 + log 5) / log 2 := by 
    field_simp [(show log 2 ≠ 0 by positivity)]
    <;> nlinarith 
  have h7 : 1 - (log 2 + 2 * log 5) / log 5 = - (log 2 + log 5) / log 5 := by 
    field_simp [(show log 5 ≠ 0 by positivity)]
    <;> nlinarith 
  rw [h6, h7]
  have h8 : log 2 + log 5 = log 10 := by 
    calc 
      log 2 + log 5 = log (2 * 5) := by rw [log_mul (by norm_num) (by norm_num)]
      _ = log 10 := by norm_num 
  field_simp [(show log 2 ≠ 0 by positivity), (show log 5 ≠ 0 by positivity), 
      (show log 2 + log 5 ≠ 0 by 
          by_contra h 
          have h9 : log 2 + log 5 = 0 := by linarith 
          have h10 : log 10 = 0 := by 
            linarith [h8, h9] 
          have h11 : log 10 > 0 := by 
            apply log_pos 
            all_goals linarith 
          linarith 
      ), h8] 
  <;> nlinarith [h8, show log 10 > 0 by apply log_pos; all_goals linarith]