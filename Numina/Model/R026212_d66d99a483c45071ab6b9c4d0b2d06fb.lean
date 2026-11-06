import Mathlib

theorem inequalities_257683 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    x ^ 2 + 2 * y ^ 2 + 3 * z ^ 2 > x * y + 3 * y * z + z * x := by
  nlinarith [sq_nonneg (x - y / 2 - z / 2), sq_nonneg (y - 3 * z / 2), sq_nonneg (x - 3 * y), sq_nonneg (y - 2 * z), sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (x - z), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]