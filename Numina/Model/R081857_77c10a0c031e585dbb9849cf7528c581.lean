import Mathlib

theorem algebra_280258 (x : ℝ) (hx : x > 0) (h : 12 + 2 * x = 6 + 2.5 * x) :
    6 + 2.5 * x = 36 := by
  have eq1 : x = 12 := by
    norm_num at h 
    linarith
  rw [eq1]
  norm_num