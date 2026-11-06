import Mathlib

theorem inequalities_294419 (x : ℝ) (hx : |x| ≤ 2) :
    |3 * x - x ^ 3| ≤ 2 := by
  have h1 : -2 ≤ x := by linarith [abs_le.mp hx]
  have h2 : x ≤ 2 := by linarith [abs_le.mp hx]
  have h3 : -2 ≤ 3 * x - x^3 := by
    nlinarith [sq_nonneg (x + 1), sq_nonneg (x - 2), sq_nonneg (x - 1), sq_nonneg (x + 2)]
  have h4 : 3 * x - x^3 ≤ 2 := by
    nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 2), sq_nonneg (x - 1), sq_nonneg (x + 2)]
  apply abs_le.mpr
  constructor
  · linarith
  · linarith