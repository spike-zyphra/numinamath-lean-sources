import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_318257 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
  (h : 4 * x + 5 * y + 8 * z = 30) :
  8 * x ^ 2 + 15 * y ^ 2 + 48 * z ^ 2 ≥ 180 := by
  nlinarith [sq_nonneg (x - 3), sq_nonneg (y - 2), sq_nonneg (z - 1),
    h, sq_nonneg (4 * x - 12), sq_nonneg (5 * y - 10), sq_nonneg (8 * z - 8)]