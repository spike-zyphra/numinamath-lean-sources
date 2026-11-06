import Mathlib

theorem algebra_251789 (x : ℝ) :
    abs (3 * x - 8) - abs (3 * x - 2) = 6 ↔ x ≤ 2 / 3 := by 
  constructor
  · -- Forward direction: Assume abs (3 * x - 8) - abs (3 * x - 2) = 6, prove x ≤ 2 / 3
    intro h
    by_cases h1 : 3 * x - 8 ≥ 0
    · -- Case 1: 3x - 8 ≥ 0, so |3x-8| = 3x-8
      rw [abs_of_nonneg h1] at h
      by_cases h2 : 3 * x - 2 ≥ 0
      · -- Case 1a: 3x - 2 ≥ 0, so |3x-2| = 3x-2
        rw [abs_of_nonneg h2] at h
        linarith
      · -- Case 1b: 3x - 2 < 0, so |3x-2| = -(3x-2)
        rw [abs_of_neg (lt_of_not_ge h2)] at h
        linarith
    · -- Case 2: 3x - 8 < 0, so |3x-8| = -(3x-8)
      rw [abs_of_neg (lt_of_not_ge h1)] at h
      by_cases h2 : 3 * x - 2 ≥ 0
      · -- Case 2a: 3x - 2 ≥ 0, so |3x-2| = 3x-2
        rw [abs_of_nonneg h2] at h
        linarith
      · -- Case 2b: 3x - 2 < 0, so |3x-2| = -(3x-2)
        rw [abs_of_neg (lt_of_not_ge h2)] at h
        linarith
  · -- Backward direction: Assume x ≤ 2 / 3, prove abs (3 * x - 8) - abs (3 * x - 2) = 6
    intro h
    have h1 : 3 * x - 2 ≤ 0 := by linarith
    have h2 : 3 * x - 8 ≤ 0 := by linarith
    rw [abs_of_nonpos h2, abs_of_nonpos h1]
    linarith