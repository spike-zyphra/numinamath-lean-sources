import Mathlib

theorem algebra_292793 (v : ℝ) (h : v > 0) (h1 : 2 * v = 50 * (41 - 1)) :
    60 * v = 60000 := by
  have eq1 : v = 1000 := by
    linarith
  rw [eq1]
  norm_num