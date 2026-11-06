import Mathlib

theorem algebra_154852 (x : ℝ) :
    2 * x ^ 2 - 6 * x ≥ 0 ↔ x ≤ 0 ∨ x ≥ 3 := by
  constructor
  · -- First, prove the forward direction: if 2x^2 - 6x ≥ 0, then x ≤ 0 or x ≥ 3.
    intro h
    have h1 : 2 * x ^ 2 - 6 * x ≥ 0 := by linarith
    have h2 : x * (x - 3) ≥ 0 := by nlinarith
    by_cases h3 : x ≤ 0
    · -- If x ≤ 0, then the first disjunction is true.
      left
      exact h3
    · -- If x > 0, then we need to prove x ≥ 3.
      have h4 : x > 0 := by linarith
      right
      nlinarith [sq_nonneg (x - 3), sq_nonneg (x), h4]
  · -- Now prove the backward direction: if x ≤ 0 or x ≥ 3, then 2x^2 - 6x ≥ 0.
    rintro (h | h)
    · -- Case 1: x ≤ 0.
      nlinarith [sq_nonneg (x - 3), sq_nonneg (x), h]
    · -- Case 2: x ≥ 3.
      nlinarith [sq_nonneg (x - 3), sq_nonneg (x), h]