import Mathlib

theorem algebra_7914 (x : ℝ) : abs (x - 2) + abs (x + 1) = 4 ↔ x = -3/2 ∨ x = 5/2 := by
  constructor
  · -- Assume abs (x - 2) + abs (x + 1) = 4, prove x = -3/2 ∨ x = 5/2
    intro h
    by_cases h1 : x ≥ 2
    · -- Case 1: x ≥ 2
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at h
      right
      linarith
    · -- Case -1 ≤ x < 2
      by_cases h2 : x ≥ -1
      · -- Case -1 ≤ x < 2
        rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)] at h
        exfalso
        linarith
      · -- Case x < -1
        rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)] at h
        left
        linarith
  · -- Assume x = -3/2 ∨ x = 5/2, prove abs (x - 2) + abs (x + 1) = 4
    rintro (h | h)
    · -- Case x = -3/2
      rw [h]
      norm_num [abs_of_nonpos]
    · -- Case x = 5/2
      rw [h]
      norm_num [abs_of_nonneg]
      all_goals norm_num [abs_of_nonneg]