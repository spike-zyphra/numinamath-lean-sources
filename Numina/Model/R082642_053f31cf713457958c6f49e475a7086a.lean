import Mathlib

open Real Set

theorem inequalities_322330 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : 5 * x + 16 * y + 33 * z ≥ 136) :
    x ^ 3 + y ^ 3 + z ^ 3 + x ^ 2 + y ^ 2 + z ^ 2 ≥ 50 := by
  nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 2), sq_nonneg (z - 3),
    sq_nonneg (5 * x + 16 * y + 33 * z - 136),
    mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]