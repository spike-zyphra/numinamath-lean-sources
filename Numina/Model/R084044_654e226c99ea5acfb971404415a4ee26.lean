import Mathlib

theorem algebra_317064 (x1 x2 x3 : ℝ) (h : x1^2 + x2^2 + x3^2 + x1 * x2 + x2 * x3 = 2) :
    |x2| ≤ 2 := by
  have h1 : (x1 + x2 / 2) ^ 2 + (x3 + x2 / 2) ^ 2 ≥ 0 := by
    nlinarith [sq_nonneg (x1 + x2 / 2), sq_nonneg (x3 + x2 / 2)]
  have h2 : (x1 + x2 / 2) ^ 2 + (x3 + x2 / 2) ^ 2 = 2 - x2^2 / 2 := by
    nlinarith
  have h3 : 2 - x2^2 / 2 ≥ 0 := by
    nlinarith [h2, h1]
  have h4 : x2^2 ≤ 4 := by
    nlinarith
  have h5 : x2 ≤ 2 := by
    nlinarith [sq_nonneg (x2 - 2), sq_nonneg (x2 + 2)]
  have h6 : x2 ≥ -2 := by
    nlinarith [sq_nonneg (x2 - 2), sq_nonneg (x2 + 2)]
  apply abs_le.mpr
  constructor
  · linarith
  · linarith