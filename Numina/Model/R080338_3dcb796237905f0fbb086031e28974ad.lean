import Mathlib

theorem algebra_300837 (x y : ℝ) (h : x^2 + x * y + y^2 - 2 = 0) :
    2 / 3 ≤ x^2 - x * y + y^2 ∧ x^2 - x * y + y^2 ≤ 6 := by
  have h1 : x^2 + x * y + y^2 = 2 := by linarith
  constructor
  · -- Proof that 2/3 ≤ x^2 - x * y + y^2
    nlinarith [sq_nonneg (x + y), sq_nonneg (x - y), sq_nonneg (x^2 - y^2), sq_nonneg (x * y - 1)]
  · -- Proof that x^2 - x * y + y^2 ≤ 6
    nlinarith [sq_nonneg (x + y), sq_nonneg (x - y), sq_nonneg (x^2 - y^2), sq_nonneg (x * y - 1)]