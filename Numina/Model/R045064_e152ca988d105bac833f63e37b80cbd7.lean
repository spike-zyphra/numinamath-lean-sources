import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_234339 (x : ℝ) :
  abs (x^2 - x) ≤ 2*x^2 - 3*x + 1 ↔ x ≤ 1/3 ∨ x ≥ 1 := by
  constructor
  · -- Assume abs (x^2 - x) ≤ 2*x^2 - 3*x + 1, prove x ≤ 1/3 ∨ x ≥ 1
    intro h
    have h1 : - (2 * x^2 - 3 * x + 1) ≤ x^2 - x := by
      cases abs_le.mp h with
      | intro h2 h3 =>
        nlinarith
    have h2 : 3 * x ^ 2 - 4 * x + 1 ≥ 0 := by
      nlinarith [h1]
    by_cases h3 : x ≤ 1 / 3
    · left
      exact h3
    · -- Assume not x ≤ 1/3, so x > 1/3
      have h4 : x > 1 / 3 := by linarith
      right
      nlinarith [sq_nonneg (x - 1), sq_nonneg (x - 1/3)]
  · -- Assume x ≤ 1/3 ∨ x ≥ 1, prove abs (x^2 - x) ≤ 2*x^2 - 3*x + 1
    rintro (h | h)
    · -- Assume x ≤ 1/3
      have h2 : 3 * x ^ 2 - 4 * x + 1 ≥ 0 := by
        nlinarith [sq_nonneg (x - 1/3), sq_nonneg (x - 1)]
      have h1 : - (2 * x ^ 2 - 3 * x + 1) ≤ x^2 - x := by
        nlinarith [h2]
      have h4 : x^2 - x ≤ 2 * x ^ 2 - 3 * x + 1 := by
        nlinarith [sq_nonneg (x - 1)]
      apply abs_le.mpr
      constructor <;> nlinarith
    · -- Assume x ≥ 1
      have h2 : 3 * x ^ 2 - 4 * x + 1 ≥ 0 := by
        nlinarith [sq_nonneg (x - 1/3), sq_nonneg (x - 1)]
      have h1 : - (2 * x ^ 2 - 3 * x + 1) ≤ x^2 - x := by
        nlinarith [h2]
      have h4 : x^2 - x ≤ 2 * x ^ 2 - 3 * x + 1 := by
        nlinarith [sq_nonneg (x - 1)]
      apply abs_le.mpr
      constructor <;> nlinarith