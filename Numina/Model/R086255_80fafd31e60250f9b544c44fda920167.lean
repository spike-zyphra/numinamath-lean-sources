import Mathlib

theorem algebra_308101 : ∀ x y : ℝ, 3 * x ^ 2 - 8 * x * y + 9 * y ^ 2 - 4 * x + 6 * y + 13 > 0 := by
  intro x y
  nlinarith [sq_nonneg (x - 4 / 3 * y - 2 / 3), sq_nonneg (y + 1 / 11), sq_nonneg (x - 2 / 3 * y + 8 / 11), sq_nonneg (3 * x - 4 * y - 2), sq_nonneg ((2 / 11) * y - 7 / 11), sq_nonneg (x * y - 2 / 3 * x), sq_nonneg (x * y - 4 / 3 * x), sq_nonneg (x * y - 2), sq_nonneg (x * y - 4), sq_nonneg (x * 3 + 2 / 3 * y), sq_nonneg (y * 2 - 3 / 2), sq_nonneg (y), sq_nonneg (x - 2 * y), sq_nonneg (x + 2 * y), sq_nonneg (x - 2), sq_nonneg (y - 1)]