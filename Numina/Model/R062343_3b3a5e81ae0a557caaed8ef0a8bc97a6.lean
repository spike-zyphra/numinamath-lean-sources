import Mathlib

theorem inequalities_4273 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h1 : y ^ 2 ≤ z ^ 2 + x ^ 2) (h2 : z ^ 2 ≤ x ^ 2 + y ^ 2) :
    x ^ 4 + x ^ 2 * (y + z) ^ 2 - 2 * (y - z) ^ 2 * (y + z) ^ 2 > 0 := by
  nlinarith [sq_nonneg (x ^ 2), sq_nonneg (y ^ 2 - z ^ 2), sq_nonneg (y * z), sq_nonneg (x * y - x * z), sq_nonneg (y - z), sq_nonneg (x - y), sq_nonneg (x - z), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]