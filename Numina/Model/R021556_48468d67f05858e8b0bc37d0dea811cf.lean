import Mathlib

theorem inequalities_8347 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x * y * z ≥ x * y + y * z + z * x) : x * y * z ≥ 3 * (x + y + z) := by
  nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
          sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          mul_pos hx hy, mul_pos hx hz, mul_pos hy hz,
          mul_pos (show 0 < x by linarith) (show 0 < y * z by nlinarith),
          mul_pos (show 0 < y by linarith) (show 0 < x * z by nlinarith),
          mul_pos (show 0 < z by linarith) (show 0 < x * y by nlinarith)]