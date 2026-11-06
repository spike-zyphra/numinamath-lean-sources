import Mathlib

theorem algebra_10408 {D : ℝ} (h : 4 * 1.25 = 3 * D) : D = 1 + 2 / 3 := by 
  have h1 : D = (4 * 1.25) / 3 := by
    linarith
  rw [h1]
  norm_num