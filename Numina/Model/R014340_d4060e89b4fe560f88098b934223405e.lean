import Mathlib

open Real Set

theorem inequalities_29921 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x^2 * y^2 + x^2 * y + x * y^2 ≤ x^4 * y + x + y^4 := by
  nlinarith [sq_nonneg (x^2 - y^2), sq_nonneg (y^2 - x), sq_nonneg (x - y),
          sq_nonneg (x * y - 1), sq_nonneg (x - y^2), sq_nonneg (y - x^2),
          mul_nonneg hx hy, sq_nonneg (x * y - y), sq_nonneg (x * y - x),
          sq_nonneg (x^2 - y), sq_nonneg (y^2 - x),
          mul_nonneg (show 0 ≤ x by linarith) (show 0 ≤ y by linarith),
          mul_nonneg (show 0 ≤ x by linarith) (show 0 ≤ y ^ 2 by positivity),
          mul_nonneg (show 0 ≤ y by linarith) (show 0 ≤ x ^ 2 by positivity)
          ]