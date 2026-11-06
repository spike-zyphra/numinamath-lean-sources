import Mathlib

theorem algebra_93893 (d t : ℝ) (ht : t > 0) (h : d = 16 * t ^ 2) (h' : t + d / 1120 = 7.7) :
    d = 784 := by 
  rw [h] at h'
  ring_nf at h'
  nlinarith [sq_nonneg (t - 7), sq_nonneg (d - 784), Real.sq_sqrt (show (0 : ℝ) ≤ 7056 by norm_num)]