import Mathlib

theorem inequalities_323171 (a b : ℝ) (h : a < b) :
    a^3 - 3 * a ≤ b^3 - 3 * b + 4 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + 1), sq_nonneg (b - 1), sq_nonneg (a - 1), sq_nonneg (b + 1), sq_nonneg (a - b), sq_nonneg (a^2 - b^2), sq_nonneg (a^2 + b^2 - 2)]