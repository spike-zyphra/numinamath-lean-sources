import Mathlib

theorem algebra_188303 {a b : ℝ} (N : ℝ) (hN : N = 4 * a^2 - 12 * a * b + 13 * b^2 - 6 * a + 4 * b + 13) :
    N > 0 := by
  rw [hN]
  nlinarith [sq_nonneg (a - (3 * b + 3 / 2) / 2), sq_nonneg (b + 14 / 43), sq_nonneg (a - ( (3 * b) / 2 + 3 / 4)), sq_nonneg (b - (-14 / 43)), sq_nonneg (a - ( (3 * b) / 2 - 3 / 4)), sq_nonneg (a - ( (3 * b) / 2 + 1)), sq_nonneg (a - 1)]