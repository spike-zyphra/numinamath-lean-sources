import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_253527 (x : ℝ) : x^2 - 2 * abs x < 3 ↔ -3 < x ∧ x < 3 := by
  constructor
  · -- Assume x^2 - 2 * |x| < 3, prove -3 < x ∧ x < 3
    intro h
    by_cases h1 : x ≥ 0
    · -- Case 1: x >= 0, so |x| = x
      rw [abs_of_nonneg h1] at h
      constructor
      · nlinarith
      · nlinarith
    · -- Case 2: x < 0, so |x| = -x
      rw [abs_of_neg (lt_of_not_ge h1)] at h
      constructor
      · nlinarith
      · nlinarith
  · -- Assume -3 < x ∧ x < 3, prove x^2 - 2 * |x| < 3
    rintro ⟨h1, h2⟩
    by_cases h3 : x ≥ 0
    · -- Case 1: x >= 0, so |x| = x
      rw [abs_of_nonneg h3]
      nlinarith
    · -- Case 2: x < 0, so |x| = -x
      rw [abs_of_neg (lt_of_not_ge h3)]
      nlinarith
  all_goals linarith