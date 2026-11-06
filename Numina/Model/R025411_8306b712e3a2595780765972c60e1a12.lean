import Mathlib

theorem algebra_103014 (a b : ℝ) (h : a^3 + b^3 - 6 * a * b = -11) :
    -7 / 3 < a + b ∧ a + b < -2 := by
  constructor
  · -- Prove the first part: -7/3 < a + b
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b + 4), sq_nonneg (a - 2), sq_nonneg (b - 2), sq_nonneg (a + b - 2), sq_nonneg (a + b + 2), sq_nonneg (a^2 - b^2)]
  · -- Prove the second part: a + b < -2
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b + 4), sq_nonneg (a - 2), sq_nonneg (b - 2), sq_nonneg (a + b - 2), sq_nonneg (a + b + 2), sq_nonneg (a^2 - b^2)]