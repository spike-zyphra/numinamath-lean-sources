import Mathlib

theorem inequalities_599514 (a b : ℝ) (h : a ^ 2 + b ^ 2 = 5) :
    -5 ≤ a + 2 * b ∧ a + 2 * b ≤ 5 := by
  have h1 : (a + 2 * b) ^ 2 ≤ 25 := by
    nlinarith [sq_nonneg (a - b * 2), sq_nonneg (b - a * 1/2), sq_nonneg (a * 2 - b), sq_nonneg (a * 1/2 - b * 1), sq_nonneg (a * 2 + b), sq_nonneg (a - 2), sq_nonneg (b - 1), sq_nonneg (a * 1/5), sq_nonneg (b * 2/5), h]
  constructor
  · nlinarith [sq_nonneg (a + 2 * b), h1]
  · nlinarith [sq_nonneg (a + 2 * b), h1]
  all_goals nlinarith