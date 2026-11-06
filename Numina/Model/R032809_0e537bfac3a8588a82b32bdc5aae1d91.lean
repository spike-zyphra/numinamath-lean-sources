import Mathlib

theorem inequalities_228588 (a : ℝ) : 2 * a^4 + 1 ≥ 2 * a^3 + a^2 := by
  nlinarith [sq_nonneg (a ^ 2 - a), sq_nonneg (a - 1), sq_nonneg (2 * a + 1),
          sq_nonneg (a ^ 2 - a - 1), sq_nonneg (a + 1/2), sq_nonneg (a -1),
          sq_nonneg (2*a^2 + 2*a + 1), sq_nonneg ((a - 1)^2)]