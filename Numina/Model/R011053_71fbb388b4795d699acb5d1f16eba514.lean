import Mathlib

theorem algebra_94321 (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0)
(h : (1 / 3) * x + (3 + 1 / 2) * y = (3 / 4) * x + (1 / 2) * y)
(h' : y = (1 / 4)) :
x = 1 + 4 / 5 := by
  rw [h'] at h 
  linarith