import Mathlib

theorem algebra_171906 {x : ℝ} (hx : x > 0) (h : (1 + 1640 / 100) * x = x * 365.2425) :
    x / 365.2425 = 22 := by
  norm_num at h 
  nlinarith