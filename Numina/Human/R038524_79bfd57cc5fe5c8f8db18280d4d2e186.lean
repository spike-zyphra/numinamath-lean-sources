import Mathlib

theorem algebra_282606 (d : ℝ) (h : d = 100) (h' : 4 / 5 * d = x) :
x = 80 := by
  rw [h] at h'
  linarith