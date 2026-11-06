import Mathlib

open Real

theorem algebra_190479 : logb 2 80 / logb 40 2 - logb 2 160 / logb 20 2 = 2 := by
  have h1 : logb 2 80 = log 80 / log 2 := by
    field_simp [logb]

  have h2 : logb 40 2 = log 2 / log 40 := by
    field_simp [logb]

  have h3 : logb 2 160 = log 160 / log 2 := by
    field_simp [logb]

  have h4 : logb 20 2 = log 2 / log 20 := by
    field_simp [logb]

  have h5 : log 80 = 4 * log 2 + log 5 := by
    rw [show (80 : ℝ) = 2 ^ 4 * 5 by norm_num]
    have h1 : log (2 ^ 4 * 5) = log (2 ^ 4) + log 5 := by
      rw [log_mul (by positivity) (by positivity)]
    rw [h1]
    have h2 : log (2 ^ 4) = 4 * log 2 := by
      simp [log_pow]
    rw [h2]

  have h6 : log 40 = 3 * log 2 + log 5 := by
    rw [show (40 : ℝ) = 2 ^ 3 * 5 by norm_num]
    have h1 : log (2 ^ 3 * 5) = log (2 ^ 3) + log 5 := by
      rw [log_mul (by positivity) (by positivity)]
    rw [h1]
    have h2 : log (2 ^ 3) = 3 * log 2 := by
      simp [log_pow]
    rw [h2]

  have h7 : log 160 = 5 * log 2 + log 5 := by
    rw [show (160 : ℝ) = 2 ^ 5 * 5 by norm_num]
    have h1 : log (2 ^ 5 * 5) = log (2 ^ 5) + log 5 := by
      rw [log_mul (by positivity) (by positivity)]
    rw [h1]
    have h2 : log (2 ^ 5) = 5 * log 2 := by
      simp [log_pow]
    rw [h2]

  have h8 : log 20 = 2 * log 2 + log 5 := by
    rw [show (20 : ℝ) = 2 ^ 2 * 5 by norm_num]
    have h1 : log (2 ^ 2 * 5) = log (2 ^ 2) + log 5 := by
      rw [log_mul (by positivity) (by positivity)]
    rw [h1]
    have h2 : log (2 ^ 2) = 2 * log 2 := by
      simp [log_pow]
    rw [h2]

  rw [h1, h2, h3, h4, h5, h6, h7, h8]
  field_simp
  ring