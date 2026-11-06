import Mathlib

theorem algebra_288847 {x y : ℝ} (h : x * 3 = y * 5) (h' : y = x - 8) :
    y = 12 := by
  rw [h'] at h
  linarith