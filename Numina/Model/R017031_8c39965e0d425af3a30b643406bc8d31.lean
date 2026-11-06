import Mathlib

theorem algebra_291168 {x : ℝ} (hx : x > 0) (h : 3 * (x - 9.4) = x * (2 / 3) + x * (3 / 4) + x * (4 / 5)) :
    x = 36 := by
  norm_num at h 
  linarith