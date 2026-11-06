import Mathlib

theorem inequalities_276840 (a b c : ℝ) :
    a^2 + b^2 + c^2 + 3 ≥ 2 * (a + b + c) := by
  suffices (a - 1) ^ 2 + (b - 1) ^ 2 + (c - 1) ^ 2 ≥ 0 by
    nlinarith
  nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]