import Mathlib

theorem algebra_7937 (x : ℝ) (a b : ℝ)
    (ha : a = 2 * x) (hb : b = 4 - 2 * x) (h : a < b) (h' : b - a = 8) :
    x = -1 := by
  rw [ha, hb] at h'
  linarith