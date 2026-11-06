import Mathlib

open Real

theorem inequalities_3900 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
  x^4 * y + y^4 * x + z^4 * x + x^4 * z + y^4 * z + z^4 * y + 3 * (x^2 * y^2 * z + y^2 * z^2 * x + z^2 * x^2 * y) ≥ 4 * (x^3 * y * z + y^3 * z * x + z^3 * x * y) := by
  nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y), sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), mul_nonneg hx hy, mul_nonneg hy hz, mul_nonneg hz hx, sq_nonneg (x* (x - y)), sq_nonneg (x * (x - z)), sq_nonneg (y * (y - z)), sq_nonneg (y * (y - x)), sq_nonneg (z * (z - x)), sq_nonneg (z * (z - y)), mul_nonneg (show 0 ≤ x * y by nlinarith) (show 0 ≤ y * z by nlinarith), mul_nonneg (show 0 ≤ x * y by nlinarith) (show 0 ≤ z * x by nlinarith), mul_nonneg (show 0 ≤ y * z by nlinarith) (show 0 ≤ z * x by nlinarith), sq_nonneg (x^2 - y^2), sq_nonneg (y^2 - z^2), sq_nonneg (z^2 - x^2), sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y)]