import Mathlib

theorem algebra_302143 (x y : ℝ) (h : 1 ≤ x^2 + 4 * y^2 ∧ x^2 + 4 * y^2 ≤ 2) :
    1 / 2 ≤ x^2 - 2 * x * y + 4 * y^2 ∧ x^2 - 2 * x * y + 4 * y^2 ≤ 3 := by
  constructor
  · -- Prove the lower bound: 1/2 ≤ x^2 - 2*x*y + 4*y^2
    nlinarith [sq_nonneg (x - 2 * y), sq_nonneg (x + 2 * y), sq_nonneg (x - 4 * y), sq_nonneg (x - y), sq_nonneg (2 * x - 4 * y), sq_nonneg (x + 2 * y - x), sq_nonneg (x - 2 * y - (x + 2 * y)), sq_nonneg (2 * y - x), sq_nonneg (x - 2 * y + 1), sq_nonneg (x + 2 * y - 1), h.1, h.2]
  · -- Prove the upper bound: x^2 - 2*x*y + 4*y^2 ≤ 3
    nlinarith [sq_nonneg (x - 2 * y), sq_nonneg (x + 2 * y), sq_nonneg (x - 4 * y), sq_nonneg (x - y), sq_nonneg (2 * x - 4 * y), sq_nonneg (x + 2 * y - x), sq_nonneg (x - 2 * y - (x + 2 * y)), sq_nonneg (2 * y - x), sq_nonneg (x - 2 * y + 1), sq_nonneg (x + 2 * y - 1), h.1, h.2]