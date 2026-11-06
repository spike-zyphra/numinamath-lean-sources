import Mathlib

theorem inequalities_598384 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    ((x + y) / 2) ^ 2 * ((y + z) / 2) ^ 2 * ((z + x) / 2) ^ 2 ≥
    x * y * z * ((x + y + z) / 3) ^ 3 := by
  nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
          sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          sq_nonneg (x * (x - y)), sq_nonneg (x * (x - z)), sq_nonneg (y * (y - x)), sq_nonneg (y * (y - z)), sq_nonneg (z * (z - x)), sq_nonneg (z * (z - y)),
          mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, mul_nonneg (show 0 ≤ x * y by positivity) (show 0 ≤ x * y * z by positivity)]