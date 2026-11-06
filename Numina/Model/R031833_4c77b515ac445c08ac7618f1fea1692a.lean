import Mathlib

theorem algebra_309762 (x y : ℝ) (h : x^2 + y^2 + 5 * x ≤ 0) :
    3 * x + 4 * y ≤ 5 ∧ 3 * x + 4 * y ≥ -20 := by
  constructor
  · -- First, prove 3 * x + 4 * y ≤ 5.
    nlinarith [sq_nonneg (x + 1), sq_nonneg (y - 2), sq_nonneg (x - (-4)), sq_nonneg (y + 2), sq_nonneg ((x + 5/2) * 4 - 3 * y), sq_nonneg ((x + 1) * 4 * 25 - (y - 2) * 15)]
  · -- Now prove 3 * x + 4 * y ≥ -20.
    nlinarith [sq_nonneg (x + 4), sq_nonneg (y + 2), sq_nonneg (x - (-1)), sq_nonneg (y - 2), sq_nonneg ((x + 5/2) * 4 - 3 * y), sq_nonneg ((x + 4) * 25 + (y + 2) * 25 - (0:ℝ))]