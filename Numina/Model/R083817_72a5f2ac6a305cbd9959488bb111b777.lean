import Mathlib

theorem inequalities_200123 (x : ℝ) (hx : x ≥ 0) : 3 * x^3 - 6 * x^2 + 4 ≥ 0 := by
  -- Consider x >= 0, we need to show 3x^3 -6x^2 +4 >=0.
  nlinarith [sq_nonneg (x - 4 / 3), sq_nonneg (x * (x - 4 / 3)), sq_nonneg (x * x - 2 * x), sq_nonneg (x - 2), sq_nonneg (x * x - 2 * x + 4 / 9), sq_nonneg (x * (x - 4 / 3)), sq_nonneg (x^2 - 4 / 3 * x), sq_nonneg (x * (x - 2)), sq_nonneg (x * (x^2 - 4 / 3 * x)), sq_nonneg (x - 1)]