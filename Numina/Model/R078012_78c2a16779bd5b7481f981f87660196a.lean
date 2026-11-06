import Mathlib

open Real Set

theorem algebra_179011 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x + y + z = x * y * z) :
    x ^ 2 * (y * z - 1) + y ^ 2 * (z * x - 1) + z ^ 2 * (x * y - 1) ≥ 18 := by
  nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
    sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
    sq_nonneg (x * y - 1), sq_nonneg (y * z - 1), sq_nonneg (z * x - 1),
    mul_pos hx hy, mul_pos hy hz, mul_pos hx hz]