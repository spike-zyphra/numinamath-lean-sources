import Mathlib

theorem algebra_252166 (x : ℝ) (hx : x ^ 2 ≤ 1) :
    2 * Real.sqrt (1 - x ^ 2) = x - 2 ↔ False := by
  constructor
  · -- Assume 2 * sqrt(1 - x^2) = x - 2, prove False
    intro h
    have h1 : 0 ≤ Real.sqrt (1 - x ^ 2) := Real.sqrt_nonneg (1 - x ^ 2)
    have h2 : 0 ≤ 2 * Real.sqrt (1 - x ^ 2) := by linarith [h1]
    have h3 : x - 2 ≥ 0 := by linarith [h, h2]
    have h4 : x ≥ 2 := by linarith
    nlinarith [sq_nonneg (x - 2), sq_nonneg (x - 1)]
  · -- Assume False, prove 2 * sqrt(1 - x^2) = x - 2
    intro h
    exfalso
    exact h