import Mathlib

theorem algebra_22224 (a : ℝ) (h : a * (1 + 5 / 100) ^ 14 = 452) :
    (round (a * 10) : ℝ) / 10 = 228.3 := by
  have h1 : a = (452 : ℝ) / ((1 + (5 / 100 : ℝ)) ^ 14) := by
    field_simp
    linarith
  rw [h1]
  norm_num [round_eq]
  <;> norm_num
  <;> linarith