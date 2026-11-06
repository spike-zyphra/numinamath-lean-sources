import Mathlib

open BigOperators Real Set


theorem algebra_164889 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
  (h : x^2 + y^2 = 1) :
  x * (x + y) ≤ (sqrt 2 + 1) / 2 := by
  nlinarith [sq_nonneg (x ^ 2 + y ^ 2 - 1), sq_nonneg (x - y * Real.sqrt 2), sq_nonneg (y - x * Real.sqrt 2), sq_nonneg (x ^ 2 + y ^ 2 - 1), sq_nonneg (x - y), sq_nonneg (x + y - Real.sqrt 2), Real.sqrt_nonneg 2, Real.sqrt_pos.mpr (show 0 < (2:ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (2:ℝ) by linarith), sq_nonneg (y - (Real.sqrt 2 - 1) * x), sq_nonneg (x^2 + y^2 -1), mul_nonneg hx hy, mul_nonneg (show 0 ≤ Real.sqrt 2 by positivity) (show 0 ≤ Real.sqrt 2 by positivity)
  ]