import Mathlib

theorem algebra_224054 (h : (Real.pi * (1 / 2)^2) * 100 = 10000) :
    (Real.pi * (1 + 10 / 2)^2) * 100 - 10000 = 4 := by
  nlinarith [Real.pi_gt_three, Real.pi_lt_31416]