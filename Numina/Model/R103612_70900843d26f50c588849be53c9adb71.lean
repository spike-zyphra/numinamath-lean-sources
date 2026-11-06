import Mathlib

theorem algebra_312044 (x y : ℝ) (h : x^2 + 4 * y^2 = 4) :
    x^2 + 2 * x * y + 4 * y^2 ∈ Set.Icc 2 6 := by
  have h1 : -1 ≤ x * y := by
    nlinarith [sq_nonneg (x ^ 2 + 4 * y ^ 2), sq_nonneg (x - 2 * y), sq_nonneg (x + 2 * y), sq_nonneg (2 * y + x), sq_nonneg (2 * y - x)]
  have h2 : x * y ≤ 1 := by
    nlinarith [sq_nonneg (x ^ 2 + 4 * y ^ 2), sq_nonneg (x - 2 * y), sq_nonneg (x + 2 * y), sq_nonneg (2 * y + x), sq_nonneg (2 * y - x)]
  constructor
  · -- Show that the expression is greater than or equal to 2.
    nlinarith [h, h1, h2]
  · -- Show that the expression is less than or equal to 6.
    nlinarith [h, h1, h2]