import Mathlib

theorem inequalities_267662 (a : ℝ) :
    2 * a^4 + 2 * a^2 - 1 ≥ 3 / 2 * (a^2 + a - 1) := by
  nlinarith [sq_nonneg (a^2 - 1/2), sq_nonneg (a^2 - a), sq_nonneg (a - 1/2), sq_nonneg (a^2 - a + 1/2), sq_nonneg (a^2 + a - 1), sq_nonneg (a^4 - a^2), sq_nonneg (a * (a - 1/2)), sq_nonneg (a * 1), sq_nonneg ((a - 1) * (a + 1)), sq_nonneg ((a - 1/2) * (a + 1/2)), sq_nonneg ((a - 2) * (a - 2))]