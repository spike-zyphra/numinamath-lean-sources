import Mathlib

theorem algebra_14383 {x y : ℝ} (h : x + y = 1.10) (h' : x = y + 1) :
    x = 1.05 := by
  rw [h'] at h
  have eq1 : y = 0.05 := by
    norm_num at h 
    linarith
  rw [eq1] at h'
  norm_num at h'
  linarith