import Mathlib

theorem algebra_1262 (x : ℝ): |x - 6| - |x + 4| = 10 ↔  x ≤ -4 := by
  constructor
  · -- Assume |x - 6| - |x + 4| = 10 prove x ≤ -4
    intro h
    by_cases h1: x ≥ 6
    · -- x >= 6
      rw [abs_of_nonneg (show x - 6 ≥ 0 by linarith), abs_of_nonneg (show x + 4 ≥ 0 by linarith)] at h
      linarith
    by_cases h2: x ≥ -4
    · -- -4 ≤ x < 6
      rw [abs_of_nonpos (show x - 6 ≤ 0 by linarith), abs_of_nonneg (show x + 4 ≥ 0 by linarith)] at h
      linarith
    · -- x < -4
      rw [abs_of_nonpos (show x - 6 ≤ 0 by linarith), abs_of_nonpos (show x + 4 ≤ 0 by linarith)] at h
      linarith
  · -- Assume x ≤ -4 prove |x - 6| - |x + 4| = 10
    intro h
    by_cases h1: x ≥ -4
    · -- x = -4
      rw [abs_of_nonpos (show x - 6 ≤ 0 by linarith), abs_of_nonneg (show x + 4 ≥ 0 by linarith)]
      linarith
    · -- x < -4
      rw [abs_of_nonpos (show x - 6 ≤ 0 by linarith), abs_of_nonpos (show x + 4 ≤ 0 by linarith)]
      linarith