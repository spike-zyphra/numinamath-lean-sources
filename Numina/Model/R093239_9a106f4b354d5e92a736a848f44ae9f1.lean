import Mathlib

theorem algebra_2497 (x : ℝ) : abs (x - 2) + 3 = 4 * abs x ↔ x = -5 / 3 ∨ x = 1 := by
  constructor
  · -- Assume abs (x - 2) + 3 = 4 * abs x, prove x = -5 / 3 ∨ x = 1
    intro h
    by_cases h1 : x ≥ 2
    · -- Case x ≥ 2
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at h
      linarith
    by_cases h2 : x ≥ 0
    · -- Case 0 ≤ x < 2
      rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)] at h
      right
      nlinarith
    · -- Case x < 0
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)] at h
      left
      nlinarith
  · -- Assume x = -5 / 3 ∨ x = 1, prove abs (x - 2) + 3 = 4 * abs x
    rintro (h | h)
    · -- Case x = -5/3
      rw [h]
      norm_num [abs]
    · -- Case x = 1
      rw [h]
      norm_num [abs]