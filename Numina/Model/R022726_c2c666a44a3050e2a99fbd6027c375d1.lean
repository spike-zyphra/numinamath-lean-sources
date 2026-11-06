import Mathlib

open Real

theorem inequalities_195935 (a c : ℝ) :
    a^4 - 4 * a * c^3 + 3 * c^4 ≥ 0 := by
  nlinarith [sq_nonneg (a - c), sq_nonneg (a + c), sq_nonneg (a^2 + 2 * a * c + 3 * c^2), sq_nonneg (c), sq_nonneg (a - 2 * c), sq_nonneg (a + 2 * c), sq_nonneg (a - c), sq_nonneg (a + c), sq_nonneg (a - 0), sq_nonneg (c - 0)]