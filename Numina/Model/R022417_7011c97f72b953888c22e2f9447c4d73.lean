import Mathlib

open Real

theorem inequalities_82261 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x + y^3) * (x^3 + y) ≥ 4 * x^2 * y^2 := by
  nlinarith [sq_nonneg (x^2 - y^2), sq_nonneg (x - y), sq_nonneg (x * y - 1), sq_nonneg (x - y^2), sq_nonneg (x^2 - y), 
          sq_nonneg (x * (x - y) + y * (y - x)), sq_nonneg (x^2 - y^2), mul_nonneg hx hy, 
          mul_nonneg (show 0 ≤ x^2 by positivity) (show 0 ≤ y^2 by positivity), 
          mul_nonneg (show 0 ≤ x by positivity) (show 0 ≤ y^3 by positivity), 
          sq_nonneg (x * y), sq_nonneg (x - y), sq_nonneg (x^3 - y^3), sq_nonneg (x * y - 2 * x^2), sq_nonneg (x * y - 2 * y^2)]