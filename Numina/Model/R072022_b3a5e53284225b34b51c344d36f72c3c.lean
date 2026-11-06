import Mathlib

theorem algebra_322883 (a b : ℝ) (h : a^2 + a * b + b^2 = 1) :
    a * b - a^2 - b^2 ≤ -1 / 3 ∧ a * b - a^2 - b^2 ≥ -3 := by
  have h1 : a * b - a^2 - b^2 ≤ -1 / 3 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a - 2 * b), sq_nonneg (2 * a - b), sq_nonneg (a + b - 2 / 3), sq_nonneg (a - b - 2 / 3)]
  have h2 : a * b - a^2 - b^2 ≥ -3 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a - 2 * b), sq_nonneg (2 * a - b), sq_nonneg (a * b + 1), sq_nonneg (a + b - 1), sq_nonneg (a + b + 1)]
  constructor
  · linarith
  · linarith