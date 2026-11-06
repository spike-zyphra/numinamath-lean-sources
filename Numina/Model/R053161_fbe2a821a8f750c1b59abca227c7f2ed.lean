import Mathlib

theorem inequalities_51493 (a : ℝ) :
    (a^3 + a^2 + 3)^2 > 4 * a^3 * (a - 1)^2 := by
  nlinarith [sq_nonneg (a^3 - a^2 - 1), sq_nonneg (a^2 + 1), sq_nonneg (a - 1), sq_nonneg (a + 1), sq_nonneg (a^3 - a), sq_nonneg (a^2 - a - 1), sq_nonneg (a^3 - a^2), sq_nonneg (a^2 - a + 1), sq_nonneg (a * (a - 1)), sq_nonneg ((a - 1) * (a + 1))]