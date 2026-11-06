import Mathlib

theorem algebra_188351 {x y : ℝ} (h : x * 2 + y * 5 = 195) (h' : x = 4 * y) :
    x = 60 := by 
  rw [h'] at h
  linarith