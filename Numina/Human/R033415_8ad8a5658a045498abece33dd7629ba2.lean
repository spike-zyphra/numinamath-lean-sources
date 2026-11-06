import Mathlib

open Real

theorem algebra_190479 : logb 2 80 / logb 40 2 - logb 2 160 / logb 20 2 = 2 := by
  have h1: logb 2 80 = log 80 / log 2 := by
    rw [logb]
  have h2: logb 40 2 = log 2 / log 40 := by
    rw [logb]
  have h3: logb 2 160 = log 160 / log 2 := by
    rw [logb]
  have h4: logb 20 2 = log 2 / log 20 := by
    rw [logb]

  rw [h1, h2, h3, h4]
  field_simp
  
  have h5: log 80 = log 16 + log 5 := by
    have: (80:ℝ) = 16 * 5 := by norm_num
    rw [this]
    exact log_mul (by norm_num) (by norm_num)
  have h6: log 40 = log 8 + log 5 := by
    have: (40:ℝ) = 8 * 5 := by norm_num
    rw [this]
    exact log_mul (by norm_num) (by norm_num)
  have h7: log 160 = log 32 + log 5 := by
    have: (160:ℝ) = 32 * 5 := by norm_num
    rw [this]
    exact log_mul (by norm_num) (by norm_num)
  have h8: log 20 = log 4 + log 5 := by
    have: (20:ℝ) = 4 * 5 := by norm_num
    rw [this]
    exact log_mul (by norm_num) (by norm_num)

  rw [h5, h6, h7, h8]

  have h9: log 16 = 4 * log 2 := by
    have: (16:ℝ) = 2^4 := by norm_num
    rw [this]
    rw [log_pow]
    norm_num
  have h10: log 32 = 5 * log 2 := by
    have: (32:ℝ) = 2^5 := by norm_num
    rw [this]
    rw [log_pow]
    norm_num
  have h11: log 8 = 3 * log 2 := by
    have: (8:ℝ) = 2^3 := by norm_num
    rw [this]
    rw [log_pow]
    norm_num
  have h12: log 4 = 2 * log 2 := by
    have: (4:ℝ) = 2^2 := by norm_num
    rw [this]
    rw [log_pow]
    norm_num

  rw [h9, h10, h11, h12]
  ring