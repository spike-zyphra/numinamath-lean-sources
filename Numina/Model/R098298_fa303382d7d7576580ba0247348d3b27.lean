import Mathlib

theorem inequalities_112919 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    2 * x * y * (2 * x + y) + 6 * x * z * (2 * x + 3 * z) +
        3 * y * z * (y + 3 * z) ≥ 36 * x * y * z := by
  nlinarith [sq_nonneg (2 * x - y), sq_nonneg (2 * x - 3 * z), sq_nonneg (y - 3 * z),
          mul_pos hx hy, mul_pos hx hz, mul_pos hy hz
        ]