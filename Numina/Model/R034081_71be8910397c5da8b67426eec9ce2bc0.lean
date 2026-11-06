import Mathlib

theorem algebra_7971 (x : ℝ) : |x + 6| - |3 * x - 9| = 1 ↔ x = 1 ∨ x = 7 := by
  constructor
  · -- Assume |x + 6| - |3 * x - 9| = 1, prove x = 1 ∨ x = 7
    intro h
    by_cases h1 : x ≥ 3
    · -- Case 1: x ≥ 3
      rw [abs_of_nonneg (show x + 6 ≥ 0 by linarith), abs_of_nonneg (show 3 * x - 9 ≥ 0 by linarith)] at h
      have h2 : x = 7 := by linarith
      right
      exact h2
    · -- Case 2: x < 3
      by_cases h2 : x ≥ -6
      · -- Case 2a: -6 ≤ x < 3
        rw [abs_of_nonneg (show x + 6 ≥ 0 by linarith), abs_of_nonpos (show 3 * x - 9 ≤ 0 by linarith)] at h
        have h3 : x = 1 := by linarith
        left
        exact h3
      · -- Case 2b: x < -6
        rw [abs_of_nonpos (show x + 6 ≤ 0 by linarith), abs_of_nonpos (show 3 * x - 9 ≤ 0 by linarith)] at h
        linarith
  · -- Assume x = 1 ∨ x = 7, prove |x + 6| - |3 * x - 9| = 1
    rintro (h | h)
    · -- Case 1: x = 1
      rw [h]
      norm_num [abs_of_nonneg, abs_of_nonpos]
    · -- Case 2: x = 7
      rw [h]
      norm_num [abs_of_nonneg, abs_of_nonpos]