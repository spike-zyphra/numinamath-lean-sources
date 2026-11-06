import Mathlib

theorem inequalities_33493 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    x ^ 2 + x * y ^ 2 + x * y * z ^ 2 ≥ 4 * x * y * z - 4 := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          sq_nonneg (x - 2), sq_nonneg (y - 2), sq_nonneg (z - 2),
          mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]