import Mathlib

theorem inequalities_170321 (a b : ℝ) (h : 4 * b + a = 1) : a ^ 2 + 4 * b ^ 2 ≥ 1 / 5 := by
  have ha : a = 1 - 4 * b := by linarith
  rw [ha]
  nlinarith [sq_nonneg (b - 2 / 10), sq_nonneg ((1 - 4 * b) - 4 / 5), sq_nonneg (b - 1 / 5), sq_nonneg ((1 - 4 * b) - 1 / 5), sq_nonneg (b), sq_nonneg (1 - 4 * b)]