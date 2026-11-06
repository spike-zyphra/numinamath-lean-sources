import Mathlib

open Real

theorem algebra_228163 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x^3 + y^3 + z^3 - 3 * x * y * z = 1) :
    x^2 + y^2 + z^2 ≥ 1 := by
  nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
    sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z),
    mul_pos hx hy, mul_pos hx hz, mul_pos hy hz
  ]