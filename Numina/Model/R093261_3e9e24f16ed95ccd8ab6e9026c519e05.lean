import Mathlib

theorem algebra_150548 {x y : ℝ} (h1 : x + 3 * y + 14 ≤ 0) (h2 : x ^ 4 + 2 * x ^ 2 * y ^ 2 + y ^ 4 + 64 - 20 * x ^ 2 - 20 * y ^ 2 = 8 * x * y) :
    x = -2 ∧ y = -4 := by
  have h4 : (x + 2) ^ 2 + (y + 4) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x + 2), sq_nonneg (y + 4), sq_nonneg (x - y), sq_nonneg (x + 3 * y + 14), sq_nonneg (x + y), sq_nonneg (x - 2), sq_nonneg (y - 4)]
  have hx : x + 2 = 0 := by
    nlinarith [h4, sq_nonneg (x + 2), sq_nonneg (y + 4)]
  have hy : y + 4 = 0 := by
    nlinarith [h4, sq_nonneg (x + 2), sq_nonneg (y + 4)]
  constructor
  · linarith [hx]
  · linarith [hy]