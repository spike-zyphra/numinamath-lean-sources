import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_317355 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
  (h : x^3 + y^3 + 3 * x * y = 1) :
  x^2 * y ≤ 4 / 27 := by 
  nlinarith [sq_nonneg (x - y), sq_nonneg (x - 2 * y), sq_nonneg (2 * x - y),
    sq_nonneg (x - 1 / 3), sq_nonneg (y - 1 / 3), sq_nonneg (x + y - 4 / 3),
    sq_nonneg (x - 2 / 3), sq_nonneg (y - 2 / 3),
    sq_nonneg (x^2 - y * x), sq_nonneg (y - 2 / 3), sq_nonneg (x - 1 / 3), sq_nonneg (y - 2 / 3), mul_nonneg hx hy]