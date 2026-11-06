import Mathlib

theorem inequalities_602672 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x * y + y * z + z * x = 1) :
    4 ≤ 10 * x^2 + 10 * y^2 + z^2 := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (x - 1 / 3), sq_nonneg (y - 1 / 3), sq_nonneg (z - 4 / 3),
            sq_nonneg (x * y - 1 / 9), sq_nonneg (z - 2 * x), sq_nonneg (z - 2 * y),
            mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]