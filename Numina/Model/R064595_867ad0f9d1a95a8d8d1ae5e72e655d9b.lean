import Mathlib

theorem algebra_178368 (t : ℝ) (ht : t > 0) (h : 4 * t - 0.75 * t^2 = 3.5 * t + 0.5 * t^2 + 10) :
    t = 5 := by 
  norm_num at h 
  nlinarith [sq_nonneg (t - 5), sq_nonneg (t + 4)]