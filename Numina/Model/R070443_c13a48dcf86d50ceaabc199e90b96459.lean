import Mathlib

theorem algebra_13565 (x : ℝ) (hx : x > 0) (h : 0.90 * x ≤ 630) :
    x ≤ 700 := by
  norm_num at h 
  linarith