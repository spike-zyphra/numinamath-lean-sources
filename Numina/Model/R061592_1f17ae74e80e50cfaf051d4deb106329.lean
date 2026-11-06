import Mathlib

theorem algebra_218593 (x y : ℝ) (h : 2 * x + 8 * y = 3) :
    x ^ 2 + 4 * y ^ 2 - 2 * x ≥ -19 / 20 := by
  have h1 : y = (3 - 2 * x) / 8 := by
    linarith
  rw [h1]
  nlinarith [sq_nonneg (x - 11 / 10), sq_nonneg (x - 4 / 5), sq_nonneg (x - 7 / 5)]