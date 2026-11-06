import Mathlib

theorem algebra_152449 {x y : ℝ} (h : 8 * y ^ 4 + 4 * x ^ 2 * y ^ 2 + 4 * x * y ^ 2 + 2 * x ^ 3 + 2 * y ^ 2 + 2 * x = x ^ 2 + 1) :
    x + 2 * y ^ 2 = 1 / 2 := by
  nlinarith [sq_nonneg (2 * y ^ 2 - 1 / 2), sq_nonneg (x - 1 / 2), sq_nonneg (x * y - 1 / 4), sq_nonneg (x * y + 1 / 4), sq_nonneg (x + 2 * y ^ 2 - 1 / 2), sq_nonneg (y ^ 2 * (y ^ 2 - 1 / 4)), sq_nonneg (x + 2 * y ^ 2), sq_nonneg (x * y + y ^ 2 * (y ^ 2)), sq_nonneg (x - y ^ 2)]