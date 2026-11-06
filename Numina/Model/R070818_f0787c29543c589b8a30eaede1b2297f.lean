import Mathlib

theorem algebra_324150 (x y : ℝ) (h : x^2 + x * y + y^2 = 1) :
    -1 / 3 ≤ x^2 - x * y + y^2 ∧ x^2 - x * y + y^2 ≤ 3 := by
  constructor
  · -- Prove the lower bound
    nlinarith [sq_nonneg (x + y), sq_nonneg (x - y), sq_nonneg (x + 2 * y), sq_nonneg (y + 2 * x),
      mul_self_nonneg (x + y), mul_self_nonneg (x - y)]
  · -- Prove the upper bound
    nlinarith [sq_nonneg (x + y), sq_nonneg (x - y), sq_nonneg (x + 2 * y), sq_nonneg (y + 2 * x),
      mul_self_nonneg (x + y), mul_self_nonneg (x - y)]