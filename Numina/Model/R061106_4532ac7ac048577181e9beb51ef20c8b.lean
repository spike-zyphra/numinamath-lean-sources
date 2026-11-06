import Mathlib

theorem inequalities_27347 (a : ℝ) :
    3 * (1 + a ^ 2 + a ^ 4) ≥ (1 + a + a ^ 2) ^ 2 := by
  nlinarith [sq_nonneg (a^2 - a), sq_nonneg (a - 1), sq_nonneg (a + 1/2), sq_nonneg (a^2 - 1)]