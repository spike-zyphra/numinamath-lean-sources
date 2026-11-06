import Mathlib

theorem algebra_6052 (x y : ℝ) (h : x^2 + y^2 + 58 = 14 * x - 6 * y) : x * y = -21 := by 
  have : (x - 7) ^ 2 + (y + 3) ^ 2 = 0 := by linarith
  have hx : x = 7 := by nlinarith
  have hy : y = -3 := by nlinarith
  rw [hx, hy]
  norm_num