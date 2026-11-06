import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_145832 (x : ℝ) :
  -1/2 * x^2 + x + 15/2 ≤ 0 ↔ x ≤ -3 ∨ x ≥ 5 := by

  constructor
  · -- Assume -1/2 * x^2 + x + 15/2 ≤ 0 prove x ≤ -3 ∨ x ≥ 5
    intro h
    have h1 : -1/2 * x^2 + x + 15/2 ≤ 0 := h

    -- Convert to standard form
    have h2 : x^2 - 2 * x - 15 ≥ 0 := by
      nlinarith

    -- Factor the quadratic
    have h3 : (x - 5) * (x + 3) ≥ 0 := by
      nlinarith

    -- Now determine the possible solutions. Either both factors are non-negative or both are non-positive
    cases' (mul_nonneg_iff.mp h3) with h4 h5

    · -- Case where both factors are non-negative
      right
      linarith

    · -- Case where both factors are non-positive
      left
      linarith

  · -- Assume x ≤ -3 ∨ x ≥ 5 prove -1/2 * x^2 + x + 15/2 ≤ 0
    rintro (h | h)
    · -- Case where x ≤ -3
      have h3 : x^2 - 2 * x - 15 ≥ 0 := by
        nlinarith [h]

      -- Convert back to original form and project to the given inequality
      nlinarith

    · -- Case where x ≥ 5
      have h4 : x^2 - 2 * x - 15 ≥ 0 := by
        nlinarith [h]

      -- Convert back to original form and project to the given inequality
      nlinarith