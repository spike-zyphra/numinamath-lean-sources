import Mathlib

open Real

theorem algebra_42640 : ((4 - logb 36 4 - logb 6 18) / logb 4 3) * (logb 8 27 + logb 2 9) = 12 := by 
  have h1 : logb 36 4 = log 4 / log 36 := by
    field_simp [logb]
  have h2 : logb 6 18 = log 18 / log 6 := by
    field_simp [logb]
  have h3 : logb 4 3 = log 3 / log 4 := by
    field_simp [logb]
  have h4 : logb 8 27 = log 27 / log 8 := by
    field_simp [logb]
  have h5 : logb 2 9 = log 9 / log 2 := by
    field_simp [logb]
  have h6 : log 4 = 2 * log 2 := by 
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
    simp [log_pow]
    all_goals linarith
  have h7 : log 36 = 2 * log 2 + 2 * log 3 := by 
    rw [show (36 : ℝ) = 4 * 9 by norm_num]
    have h1 : log (4 * 9 : ℝ) = log (4 : ℝ) + log (9 : ℝ) := by
      rw [log_mul (by norm_num) (by norm_num)]
    rw [h1]
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, show (9 : ℝ) = 3 ^ 2 by norm_num]
    simp [log_pow]
    all_goals linarith
  have h8 : log 18 = log 2 + 2 * log 3 := by 
    rw [show (18 : ℝ) = 2 * 9 by norm_num]
    have h1 : log (2 * 9 : ℝ) = log (2 : ℝ) + log (9 : ℝ) := by 
      rw [log_mul (by norm_num) (by norm_num)]
    rw [h1]
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num]
    simp [log_pow]
    all_goals linarith
  have h9 : log 6 = log 2 + log 3 := by 
    rw [show (6 : ℝ) = 2 * 3 by norm_num]
    simp [log_mul]
    all_goals linarith
  have h10 : log 8 = 3 * log 2 := by 
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num]
    simp [log_pow]
    all_goals linarith
  have h11 : log 27 = 3 * log 3 := by 
    rw [show (27 : ℝ) = 3 ^ 3 by norm_num]
    simp [log_pow]
    all_goals linarith
  have h12 : log 9 = 2 * log 3 := by 
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num]
    simp [log_pow]
    all_goals linarith
  rw [h1, h2, h3, h4, h5]
  rw [h6, h7, h8, h9, h10, h11, h12]
  field_simp
  <;> ring
  all_goals linarith