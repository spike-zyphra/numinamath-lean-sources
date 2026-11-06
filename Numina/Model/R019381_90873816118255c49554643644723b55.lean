import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_183744 (x y : ℝ) :
  (|y - 3 * x| ≥ |2 * y + x| ∧ -1 ≤ y - 3 ∧ y - 3 ≤ 1) ↔
  ((2 * y + x) ^ 2 - (y - 3 * x) ^ 2 ≤ 0 ∧ 2 ≤ y ∧ y ≤ 4) := by
  constructor
  · -- Assume the first system, prove the second
    rintro ⟨h1, h2, h3⟩
    have h4 : (y - 3 * x) ^ 2 ≥ (2 * y + x) ^ 2 := by
      apply sq_le_sq.mpr
      exact h1
    have h5 : (2 * y + x) ^ 2 - (y - 3 * x) ^ 2 ≤ 0 := by
      linarith
    have h6 : 2 ≤ y := by
      linarith
    have h7 : y ≤ 4 := by
      linarith
    constructor
    · exact h5
    constructor
    · exact h6
    · exact h7
  · -- Assume the second system, prove the first
    rintro ⟨h1, h2, h3⟩
    have h4 : (y - 3 * x) ^ 2 ≥ (2 * y + x) ^ 2 := by
      linarith
    have h5 : |y - 3 * x| ≥ |2 * y + x| := by
      apply sq_le_sq.mp
      linarith
    have h8 : -1 ≤ y - 3 := by
      linarith
    have h9 : y - 3 ≤ 1 := by
      linarith
    constructor
    · exact h5
    constructor
    · exact h8
    · exact h9