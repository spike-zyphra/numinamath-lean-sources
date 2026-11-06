import Mathlib

theorem algebra_178085 (x : ℝ) :
    abs (x - 2) + abs (x - 1) + abs x + abs (x + 1) + abs (x + 2) = 6 ↔ x = 0 := by
  constructor
  · -- First, we prove that if the equation holds, then x = 0.
    intro h
    by_cases h1 : x ≥ 2
    · -- Case 1: x ≥ 2
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at h
      linarith
    by_cases h2 : x ≥ 1
    · -- Case 2: 1 ≤ x < 2
      rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at h
      linarith
    by_cases h3 : x ≥ 0
    · -- Case 3: 0 ≤ x < 1
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at h
      linarith
    by_cases h4 : x ≥ -1
    · -- Case 4: -1 ≤ x < 0
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at h
      linarith
    by_cases h5 : x ≥ -2
    · -- Case 5: -2 ≤ x < -1
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)] at h
      linarith
    · -- Case 6: x < -2
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)] at h
      linarith
  · -- Now, we prove the converse: if x = 0, then the equation holds.
    intro h
    rw [h]
    norm_num [abs_of_nonneg, abs_of_nonpos]