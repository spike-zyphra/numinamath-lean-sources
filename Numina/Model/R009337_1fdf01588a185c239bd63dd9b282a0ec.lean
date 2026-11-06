import Mathlib

theorem inequalities_57472 {a b c d : ℝ} (h : a^2 + b^2 + c^2 + d^2 = 1) :
    (1 - a) * (1 - b) ≥ c * d := by
  nlinarith [sq_nonneg (c - d), sq_nonneg (a + b - 1), sq_nonneg (c + d), sq_nonneg (a - b), sq_nonneg (a - 1), sq_nonneg (b - 1)]