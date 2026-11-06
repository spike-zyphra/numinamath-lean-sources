import Mathlib

theorem inequalities_601039 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x^2 + y^2)^2 + x^3 + y^3 + 4 * x * y^2 + x^2 + y^2 ≥ 3 * x^3 * y + 5 * x * y^2 + x * y := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (x - 2 * y), sq_nonneg (2 * x - y), sq_nonneg (x^2 - y^2), sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (x * (x - y)), sq_nonneg ((y) * (y - x)), sq_nonneg (x * y), sq_nonneg (x - y), sq_nonneg (x^2 - y * x), sq_nonneg (x - y), sq_nonneg (x * (x - y)), sq_nonneg ((y) * (y - x)), mul_nonneg hx hy, sq_nonneg (x^3 - y^2 * x), sq_nonneg ((x^2 + y^2) * (x - y)), mul_nonneg (show 0 ≤ x^2 by positivity) (show 0 ≤ y^2 by positivity), mul_nonneg hx hy, sq_nonneg (x * y), sq_nonneg (x - y)]