import Mathlib

theorem algebra_12088 (x : ℝ) (h : x * 32 = 24) (h' : x * 4 = y) :
    y = 3 := by
  have hx : x = 3 / 4 := by
    linarith
  rw [hx] at h'
  linarith