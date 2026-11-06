import Mathlib

theorem algebra_6356 {x : ℝ} (hx : x * 1.07 = 27.82) : x = 26 := by
  have h1 : x = (27.82 : ℝ) / 1.07 := by
    field_simp
    linarith
  rw [h1]
  norm_num