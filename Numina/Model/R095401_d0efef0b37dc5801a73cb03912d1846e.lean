import Mathlib

theorem inequalities_216075 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (x + 9 * y + 3 * z) * (x + 4 * y + 2 * z) * (2 * x + 12 * y + 9 * z) ≥
    1029 * x * y * z := by
  nlinarith [sq_nonneg (x - 3 * y), sq_nonneg (x - 3 * z), sq_nonneg (y - z),
          sq_nonneg (x - 6 * y), sq_nonneg (x - 2 * z), sq_nonneg (y - z / 2),
          mul_pos hx hy, mul_pos hx hz, mul_pos hy hz
          ]