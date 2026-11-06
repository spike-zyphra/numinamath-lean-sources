import Mathlib

theorem inequalities_61251 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (x + y + z) ^ 2 * (y * z + z * x + x * y) ^ 2 ≤
    3 * (y ^ 2 + y * z + z ^ 2) * (z ^ 2 + z * x + x ^ 2) *
    (x ^ 2 + x * y + y ^ 2) := by
  nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
          sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          mul_pos hx hy, mul_pos hx hz, mul_pos hy hz
          ]