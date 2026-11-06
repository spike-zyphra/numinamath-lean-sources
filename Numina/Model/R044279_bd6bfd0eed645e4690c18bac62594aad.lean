import Mathlib

theorem inequalities_4259 (x y z : ℝ)
    (hx : 0 < x)
    (hy : 0 < y)
    (hz : 0 < z)
    (hxyz : x * y * z = 1) :
    x ^ 3 + y ^ 3 + z ^ 3 + (x * y) ^ 3 + (y * z) ^ 3 + (z * x) ^ 3 ≥
    2 * (x ^ 2 * y + y ^ 2 * z + z ^ 2 * x) := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
    sq_nonneg (x * y - 1), sq_nonneg (y * z - 1), sq_nonneg (z * x - 1),
    sq_nonneg (x^2 * y - 1), sq_nonneg (y^2 * z - 1), sq_nonneg (z^2 * x - 1),
    sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
    mul_pos hx hy, mul_pos hy hz, mul_pos hz hx
  ]