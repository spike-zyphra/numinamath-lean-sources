import Mathlib

open Real

theorem calculus_14520 (x : ℝ) (hx : x > 0) (h : 4 * sqrt 2 = x * sqrt 2 + 10) :
    x = 9 * sqrt 2 := by
  have h1 : sqrt 2 > 0 := by positivity
  nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]