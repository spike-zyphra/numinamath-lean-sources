import Mathlib

theorem algebra_129439 (x y z : ℝ) (h : x^2 + y^2 + z^2 = 1) :
    x^2 + 2 * y^2 + 3 * z^2 ≤ 3 ∧ x^2 + 2 * y^2 + 3 * z^2 ≥ 1 := by
  constructor
  · -- Show that x^2 + 2y^2 + 3z^2 ≤ 3
    nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), h]
  · -- Show that x^2 + 2y^2 + 3z^2 ≥ 1
    nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), h]