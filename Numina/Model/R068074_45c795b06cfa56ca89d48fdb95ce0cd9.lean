import Mathlib

theorem algebra_317113 (x y : ℝ) (h : x^2 + x * y + y^2 - 2 = 0) :
    x^2 - x * y + y^2 ≤ 6 ∧ 2 / 3 ≤ x^2 - x * y + y^2 := by 
  constructor
  · -- Showing the upper bound (≤ 6)
    nlinarith [sq_nonneg (x + y), sq_nonneg (x - y), sq_nonneg (x * y - 2), sq_nonneg (x * y + 2)]
  · -- Showing the lower bound (≥ 2/3)
    nlinarith [sq_nonneg (x + y), sq_nonneg (x - y), sq_nonneg (x * y - 2), sq_nonneg (x * y + 2)]