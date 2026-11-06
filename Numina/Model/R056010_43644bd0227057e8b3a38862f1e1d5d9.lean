import Mathlib

theorem algebra_251817 (x : ℝ) :
    abs x + abs (7 - x) + 2 * abs (x - 2) ≠ 4 := by 
  intro h
  by_cases h1 : x ≥ 0
  · -- Case x ≥ 0
    by_cases h2 : x ≥ 2
    · -- Case x ≥ 2
      by_cases h3 : x ≥ 7
      · -- Case x ≥ 7
        rw [abs_of_nonneg (show x ≥ 0 by linarith), abs_of_nonpos (show (7 - x) ≤ 0 by linarith), abs_of_nonneg (show (x - 2) ≥ 0 by linarith)] at h
        linarith
      · -- Case 2 ≤ x < 7
        rw [abs_of_nonneg (show x ≥ 0 by linarith), abs_of_pos (show (7 - x) > 0 by linarith), abs_of_nonneg (show (x - 2) ≥ 0 by linarith)] at h
        linarith
    · -- Case 0 ≤ x < 2
      rw [abs_of_nonneg (show x ≥ 0 by linarith), abs_of_pos (show (7 - x) > 0 by linarith), abs_of_nonpos (show (x - 2) ≤ 0 by linarith)] at h
      linarith
  · -- Case x < 0
    rw [abs_of_nonpos (show x ≤ 0 by linarith), abs_of_pos (show (7 - x) > 0 by linarith), abs_of_nonpos (show (x - 2) ≤ 0 by linarith)] at h
    linarith