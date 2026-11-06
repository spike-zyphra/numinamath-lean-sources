import Mathlib

open Real

theorem inequalities_601118 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    x * (x - y) * (x - z) + y * (y - z) * (y - x) + z * (z - x) * (z - y) ≥ 0 := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), sq_nonneg (x - y + z), sq_nonneg (y - z + x), sq_nonneg (z - x + y), sq_nonneg (x - z), sq_nonneg (y - x), sq_nonneg (z - y),
          sq_nonneg (x * x - y * y), sq_nonneg (y * y - z * z), sq_nonneg (z * z - x * x),
          mul_pos hx hy, mul_pos hx hz, mul_pos hy hz,
          mul_pos (show 0 < x * y by nlinarith) (show 0 < y * z by nlinarith),
          mul_pos (show 0 < y * z by nlinarith) (show 0 < z * x by nlinarith)]