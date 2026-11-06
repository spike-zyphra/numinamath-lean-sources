import Mathlib

open Real

theorem algebra_195885 : logb 3 2 * logb 4 3 * logb 5 4 * logb 6 5 * logb 7 6 * logb 8 7 = 1 / 3 := by
  have h1 : logb 3 2 = log 2 / log 3 := by
    field_simp [logb]
  have h2 : logb 4 3 = log 3 / log 4 := by
    field_simp [logb]
  have h3 : logb 5 4 = log 4 / log 5 := by
    field_simp [logb]
  have h4 : logb 6 5 = log 5 / log 6 := by
    field_simp [logb]
  have h5 : logb 7 6 = log 6 / log 7 := by
    field_simp [logb]
  have h6 : logb 8 7 = log 7 / log 8 := by
    field_simp [logb]
  rw [h1, h2, h3, h4, h5, h6]
  have h7 : log 8 = 3 * log 2 := by
    calc
      log 8 = log (2 ^ 3) := by norm_num
      _ = 3 * log 2 := by simp [log_pow]
  have h8 : log 2 / log 3 * (log 3 / log 4) * (log 4 / log 5) * (log 5 / log 6) * (log 6 / log 7) * (log 7 / log 8) = log 2 / log 8 := by
    field_simp [(show log 3 ≠ 0 by positivity), (show log 4 ≠ 0 by positivity), (show log 5 ≠ 0 by positivity), (show log 6 ≠ 0 by positivity), (show log 7 ≠ 0 by positivity), (show log 8 ≠ 0 by positivity)]
    <;> ring
  have h9 : log 2 ≠ 0 := by positivity
  rw [h8]
  rw [h7]
  field_simp [h9]
  all_goals linarith