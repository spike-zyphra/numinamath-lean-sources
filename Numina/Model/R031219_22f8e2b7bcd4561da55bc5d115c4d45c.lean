import Mathlib

theorem algebra_2954 (x y : ℝ) :
    5 * x ^ 2 + 16 * x * y + 13 * y ^ 2 - 36 * x - 58 * y + 100 ≥ 35 := by
  have h1 : 5 * x ^ 2 + 16 * x * y + 13 * y ^ 2 - 36 * x - 58 * y + 100 ≥ 35 := by
    nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 1), sq_nonneg (5 * (x - 2) + 8 * (y - 1)), sq_nonneg (8 * (x - 2) + 13 * (y - 1)), sq_nonneg (x - 2 - (y - 1)), sq_nonneg ((x - 2) + (y - 1)), sq_nonneg ((x - 2) - 2 * (y - 1)), sq_nonneg (2 * (x - 2) + (y - 1))]
  linarith