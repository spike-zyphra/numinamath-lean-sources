import Mathlib

theorem inequalities_31070 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x * y + y * z + z * x + 2 * x * y * z = 1) :
    4 * x + y + z ≥ 2 := by
  nlinarith [sq_nonneg (2 * x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
          sq_nonneg (y - z), sq_nonneg (2 * x - y - z),
          mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]