import Mathlib

theorem inequalities_232491 (a b a1 b1 : ℝ) :
    (a * a1 + b * b1) ^ 2 ≤ (a ^ 2 + b ^ 2) * (a1 ^ 2 + b1 ^ 2) := by
  nlinarith [sq_nonneg (a * b1 - b * a1), sq_nonneg (a - b), sq_nonneg (a1 - b1), sq_nonneg (a * a1 - b * b1), sq_nonneg (a * b1 - b * a1), sq_nonneg (a * a1 + b * b1), sq_nonneg (a - b1), sq_nonneg (b - a1), sq_nonneg (a + b), sq_nonneg (a1 + b1)]