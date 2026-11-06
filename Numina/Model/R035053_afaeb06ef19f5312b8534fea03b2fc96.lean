import Mathlib

theorem algebra_288318 (x : ℝ) (h : x ≠ 0) (h' : (2 / 3) * x = 9) : x = 13.5 := by
  have h1 : x = 27 / 2 := by 
    linarith
  rw [h1]
  norm_num