import Mathlib

theorem algebra_1199 (x y : ℝ) : ((x - y)^2 - (y - x)^2)^2 = 0 := by
  have h1 : (x - y) ^ 2 = (y - x) ^ 2 := by 
    ring
  have h2 : (x - y) ^ 2 - (y - x) ^ 2 = 0 := by 
    rw [h1]
    ring
  rw [h2]
  norm_num