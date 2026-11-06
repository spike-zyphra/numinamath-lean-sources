import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_597504 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
  (h : x^2 + y^2 + z^2 + x + 2 * y + 3 * z = 13 / 4) :
  x + y + z ≤ 3 / 2 := by
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1 / 2), sq_nonneg (z - 0),
      mul_nonneg hx hy, mul_nonneg hx hz, mul_nonneg hy hz]