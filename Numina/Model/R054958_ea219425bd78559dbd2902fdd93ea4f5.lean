import Mathlib

theorem algebra_9004 (x : ℝ) : abs (2 * x + 1) + abs (x - 1) = 2 - x ↔ (x = -1 ∨ x = 0) := by
  constructor
  · -- Assume abs (2 * x + 1) + abs (x - 1) = 2 - x, prove x = -1 ∨ x = 0
    intro h
    by_cases h1 : x ≥ 1
    · -- x ≥ 1
      rw [abs_of_nonneg (show 2 * x + 1 ≥ 0 by linarith), abs_of_nonneg (show x - 1 ≥ 0 by linarith)] at h
      -- Now solve the resulting equation
      have h2 : x = 1 / 2 := by linarith
      linarith -- contradiction
    · -- x < 1
      by_cases h2 : x ≤ -1 / 2
      · -- x ≤ -1/2
        rw [abs_of_nonpos (show 2 * x + 1 ≤ 0 by linarith), abs_of_nonpos (show x - 1 ≤ 0 by linarith)] at h
        left
        linarith
      · -- -1/2 < x < 1
        rw [abs_of_nonneg (show 2 * x + 1 ≥ 0 by linarith), abs_of_nonpos (show x - 1 ≤ 0 by linarith)] at h
        right
        linarith
  · -- Assume (x = -1 ∨ x = 0), prove abs (2 * x + 1) + abs (x - 1) = 2 - x
    rintro (h | h)
    · -- x = -1
      rw [h]
      norm_num [abs_of_nonneg, abs_of_nonpos]
    · -- x = 0
      rw [h]
      norm_num [abs_of_nonneg, abs_of_nonpos]