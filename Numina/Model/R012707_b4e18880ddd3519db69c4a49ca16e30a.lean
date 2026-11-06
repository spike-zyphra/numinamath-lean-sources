import Mathlib

open Real

theorem inequalities_91341 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (3 * x + y) * (3 * y + z) * (3 * z + x) ≥ 64 * x * y * z := by
  nlinarith [mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, mul_pos (show 0 < x * y from mul_pos hx hy) (show 0 < y * z from mul_pos hy hz),
    sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
    sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
    sq_nonneg (x * (y - z)), sq_nonneg (y * (z - x)), sq_nonneg (z * (x - y))]