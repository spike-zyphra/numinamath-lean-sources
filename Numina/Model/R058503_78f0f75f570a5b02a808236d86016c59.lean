import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_305349 (x y : ℝ) (h : 3 * x + 2 * y - 1 ≥ 0) :
    x ^ 2 + y ^ 2 + 6 * x - 2 * y ≥ -66 / 13 := by
  nlinarith [sq_nonneg (x + 15 / 13), sq_nonneg (y - 29 / 13),
          sq_nonneg (3 * x + 2 * y - 1),
          sq_nonneg (x - (-15 / 13)), sq_nonneg (y - (29 / 13)),
          Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num)]