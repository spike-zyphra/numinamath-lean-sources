import Mathlib

theorem algebra_13414 (space_per_hour : ℝ) (h : space_per_hour * 24 * 12 = 16000) : round space_per_hour = 56 := by 
  have eq1 : space_per_hour = (16000 : ℝ) / 288 := by
    linarith
  rw [eq1]
  norm_num [round_eq]
  <;> norm_num