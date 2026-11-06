import Mathlib

theorem algebra_176057 (m : ℝ) (hm : m > 0) (h : 2 * Real.pi * 1000 = 4200 * (2 * Real.pi) + 3.3 * 10^5 * m) :
    m = 1.68 := by 
  nlinarith [Real.pi_pos, Real.pi_gt_three, sq_nonneg (Real.pi - 3.14)]