import Mathlib

theorem inequalities_44482 (a : ℝ) : a + a^3 - a^4 - a^6 < 1 := by
  nlinarith [sq_nonneg (a^2), sq_nonneg (a^3), sq_nonneg (a^2 - 1/2), sq_nonneg (a^2 - a), sq_nonneg (a + 1/2), sq_nonneg (a - 1/2), sq_nonneg (a^2 + 1/2), sq_nonneg (a^2 - a^2 * a), sq_nonneg (a^3 / 2), sq_nonneg (a^2 * (a^2 - a)), sq_nonneg (a^2 * (a + 1/2)), sq_nonneg (a^2 * (a - 1/2)), sq_nonneg ((a^2)^2 * a), sq_nonneg ((a + 1)^2), sq_nonneg ((a - 1)^2), sq_nonneg ((a^2 - a)^2), sq_nonneg ((a^2 + a)^2)]