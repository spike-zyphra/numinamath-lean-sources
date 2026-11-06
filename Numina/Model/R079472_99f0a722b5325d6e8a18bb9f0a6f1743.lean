import Mathlib

open Real

theorem algebra_294760 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x + 2 * y + 3 * z = 6) :
    x * y * z ≤ 4 / 3 := by
  nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 1), sq_nonneg (z - 2 / 3), 
          mul_pos hx hy, mul_pos hx hz, mul_pos hy hz,
          h]