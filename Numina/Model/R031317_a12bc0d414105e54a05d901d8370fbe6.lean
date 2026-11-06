import Mathlib

theorem algebra_323431 {x : ℝ} (hx : x ≠ 0) (h : 7 * (x / 8 + 2.50) = x) :
    x = 140 := by
  norm_num at h 
  linarith