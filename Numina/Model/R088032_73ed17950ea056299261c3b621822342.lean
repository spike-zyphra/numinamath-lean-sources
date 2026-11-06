import Mathlib

theorem algebra_215720 (x y : ℝ) (h : 3 * x + 2 * y = 1) :
    x ^ 2 + y ^ 2 ≥ 1 / 13 := by
  have h1 : y = (1 - 3 * x) / 2 := by
    linarith
  rw [h1]
  nlinarith [sq_nonneg (x - 3 / 13), sq_nonneg ((1 - 3 * x) / 2 - 2 / 13), sq_nonneg (3 * x - 2 * ((1 - 3 * x) / 2)), sq_nonneg (3 * (x - 3 / 13) + 2 * ((1 - 3 * x) / 2 - 2 / 13))]