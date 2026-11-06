import Mathlib

theorem algebra_13600 {s : ℝ} (hs : s > 0) (h : s * s = 400) : 4 * s = 80 := by 
  have h1 : s = 20 := by 
    nlinarith [sq_nonneg s, sq_pos_of_pos hs]
  linarith [h1]