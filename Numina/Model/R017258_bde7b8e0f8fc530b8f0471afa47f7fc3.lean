import Mathlib

open Real
open scoped BigOperators

theorem inequalities_598117 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    8 * (x^3 + y^3 + z^3)^2 ≥ 9 * (x^2 + y * z) * (y^2 + z * x) * (z^2 + x * y) := by
  nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
          sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          sq_nonneg (x * (x - y)), sq_nonneg (x * (x - z)),
          sq_nonneg (y * (y - x)), sq_nonneg (y * (y - z)),
          sq_nonneg (z * (z - x)), sq_nonneg (z * (z - y)),
          mul_nonneg hx hy, mul_nonneg hy hz, mul_nonneg hz hx,
          mul_nonneg (show 0 ≤ x * y by nlinarith) (show 0 ≤ y * z by nlinarith),
          mul_nonneg (show 0 ≤ x * y by nlinarith) (show 0 ≤ z * x by nlinarith),
          mul_nonneg (show 0 ≤ y * z by nlinarith) (show 0 ≤ z * x by nlinarith)
          ]