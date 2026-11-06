import Mathlib

theorem algebra_934 {x : ℝ} (hx : 3 * x ^ 2 + 4 * x - 7 = 0) :
    6 * x ^ 4 + 11 * x ^ 3 - 7 * x ^ 2 - 3 * x - 7 = 0 := by 
  have h : 6 * x ^ 4 + 11 * x ^ 3 - 7 * x ^ 2 - 3 * x - 7 = (3 * x ^ 2 + 4 * x - 7) * (2 * x ^ 2 + x + 1) := by 
    ring
  rw [h, hx]
  norm_num