import Mathlib

theorem algebra_243366 {x y : ℝ} (h1 : 12 * x ^ 2 + 4 * x * y + 3 * y ^ 2 + 16 * x = -6)
    (h2 : 4 * x ^ 2 - 12 * x * y + y ^ 2 + 12 * x - 10 * y = -7) :
    x = -3 / 4 ∧ y = 1 / 2 := by
  have hx : x = -3 / 4 := by
    nlinarith [sq_nonneg (x + (y + 4) / 6), sq_nonneg (y - 1 / 2), sq_nonneg (3*y + 4), sq_nonneg (3*x + 4)]
  have hy : y = 1 / 2 := by
    nlinarith [sq_nonneg (x + (y + 4) / 6), sq_nonneg (y - 1 / 2), sq_nonneg (3*y + 4), sq_nonneg (3*x + 4)]
  constructor
  · exact hx
  · exact hy