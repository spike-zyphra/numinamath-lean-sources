import Mathlib

theorem algebra_320824 (x y : ℝ) (M : ℝ) (hM : M = 3 * x ^ 2 - 8 * x * y + 9 * y ^ 2 - 4 * x + 6 * y + 13) :
    M > 0 := by 
  rw [hM]
  nlinarith [sq_nonneg (x - (2 + 4 * y) / 3), sq_nonneg (y + 1 / 11),
          sq_nonneg (x - 6 / 11), sq_nonneg (y + 1 / 11)]