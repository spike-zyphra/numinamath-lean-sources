import Mathlib

theorem algebra_237844 (v1 v2 : ℝ) (h1 : v1 = 15 / (3 * 60 + 30)) (h2 : v2 = 10 / (4 * 60)) :
    1 / v2 - 1 / v1 = 10 := by 
  rw [h1, h2]
  norm_num