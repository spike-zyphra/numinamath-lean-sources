import Mathlib

theorem algebra_326231 :
    IsGreatest {z : ℝ | ∃ x y, z = x + y ∧ |x + 2| + |1 - x| = 9 - |y - 5| - |1 + y|} 6 ∧
    IsLeast {z : ℝ | ∃ x y, z = x + y ∧ |x + 2| + |1 - x| = 9 - |y - 5| - |1 + y|} (-3) := by
  constructor
  · -- Show 6 is greatest
    constructor
    · -- Show 6 is in the set
      use 1, 5
      norm_num [abs_of_nonneg, abs_of_nonpos]
    · -- Show it's greatest
      intro z h
      rcases h with ⟨x, y, hz, heq⟩
      by_cases h1 : x ≥ 1
      · -- Case x ≥ 1
        by_cases h2 : y ≥ 5
        · -- Case y ≥ 5
          rw [abs_of_nonneg (show x + 2 ≥ 0 by linarith), abs_of_nonpos (show 1 - x ≤ 0 by linarith)] at heq
          rw [abs_of_nonneg (show y - 5 ≥ 0 by linarith), abs_of_nonneg (show 1 + y ≥ 0 by linarith)] at heq
          linarith
        by_cases h3 : y ≤ -1
        · -- Case y ≤ -1
          rw [abs_of_nonneg (show x + 2 ≥ 0 by linarith), abs_of_nonpos (show 1 - x ≤ 0 by linarith)] at heq
          rw [abs_of_nonpos (show y - 5 ≤ 0 by linarith), abs_of_nonpos (show 1 + y ≤ 0 by linarith)] at heq
          linarith
        · -- Case -1 < y < 5
          rw [abs_of_nonneg (show x + 2 ≥ 0 by linarith), abs_of_nonpos (show 1 - x ≤ 0 by linarith)] at heq
          rw [abs_of_nonpos (show y - 5 ≤ 0 by linarith), abs_of_nonneg (show 1 + y ≥ 0 by linarith)] at heq
          linarith
      · -- Case x < 1
        by_cases h4 : x ≥ -2
        · -- Case -2 ≤ x < 1
          by_cases h2 : y ≥ 5
          · -- Case y ≥ 5
            rw [abs_of_nonneg (show x + 2 ≥ 0 by linarith), abs_of_nonneg (show 1 - x ≥ 0 by linarith)] at heq
            rw [abs_of_nonneg (show y - 5 ≥ 0 by linarith), abs_of_nonneg (show 1 + y ≥ 0 by linarith)] at heq
            linarith
          by_cases h3 : y ≤ -1
          · -- Case y ≤ -1
            rw [abs_of_nonneg (show x + 2 ≥ 0 by linarith), abs_of_nonneg (show 1 - x ≥ 0 by linarith)] at heq
            rw [abs_of_nonpos (show y - 5 ≤ 0 by linarith), abs_of_nonpos (show 1 + y ≤ 0 by linarith)] at heq
            linarith
          · -- Case -1 < y < 5
            rw [abs_of_nonneg (show x + 2 ≥ 0 by linarith), abs_of_nonneg (show 1 - x ≥ 0 by linarith)] at heq
            rw [abs_of_nonpos (show y - 5 ≤ 0 by linarith), abs_of_nonneg (show 1 + y ≥ 0 by linarith)] at heq
            linarith
        · -- Case x < -2
          by_cases h6 : y ≥ 5
          · -- Case y ≥ 5
            rw [abs_of_nonpos (show x + 2 ≤ 0 by linarith), abs_of_nonneg (show 1 - x ≥ 0 by linarith)] at heq
            rw [abs_of_nonneg (show y - 5 ≥ 0 by linarith), abs_of_nonneg (show 1 + y ≥ 0 by linarith)] at heq
            linarith
          by_cases h7 : y ≤ -1
          · -- Case y ≤ -1
            rw [abs_of_nonpos (show x + 2 ≤ 0 by linarith), abs_of_nonneg (show 1 - x ≥ 0 by linarith)] at heq
            rw [abs_of_nonpos (show y - 5 ≤ 0 by linarith), abs_of_nonpos (show 1 + y ≤ 0 by linarith)] at heq
            linarith
          · -- Case -1 < y < 5
            rw [abs_of_nonpos (show x + 2 ≤ 0 by linarith), abs_of_nonneg (show 1 - x ≥ 0 by linarith)] at heq
            rw [abs_of_nonpos (show y - 5 ≤ 0 by linarith), abs_of_nonneg (show 1 + y ≥ 0 by linarith)] at heq
            linarith
  · -- Show -3 is the least
    constructor
    · -- Show -3 is in the set
      use -2, -1
      norm_num [abs_of_nonneg, abs_of_nonpos]
    · -- Show it's least
      intro z h
      rcases h with ⟨x, y, hz, heq⟩
      by_cases h1 : x ≥ 1
      · -- Case x ≥ 1
        by_cases h2 : y ≥ 5
        · -- Case y ≥ 5
          rw [abs_of_nonneg (show x + 2 ≥ 0 by linarith), abs_of_nonpos (show 1 - x ≤ 0 by linarith)] at heq
          rw [abs_of_nonneg (show y - 5 ≥ 0 by linarith), abs_of_nonneg (show 1 + y ≥ 0 by linarith)] at heq
          linarith
        by_cases h3 : y ≤ -1
        · -- Case y ≤ -1
          rw [abs_of_nonneg (show x + 2 ≥ 0 by linarith), abs_of_nonpos (show 1 - x ≤ 0 by linarith)] at heq
          rw [abs_of_nonpos (show y - 5 ≤ 0 by linarith), abs_of_nonpos (show 1 + y ≤ 0 by linarith)] at heq
          linarith
        · -- Case -1 < y < 5
          rw [abs_of_nonneg (show x + 2 ≥ 0 by linarith), abs_of_nonpos (show 1 - x ≤ 0 by linarith)] at heq
          rw [abs_of_nonpos (show y - 5 ≤ 0 by linarith), abs_of_nonneg (show 1 + y ≥ 0 by linarith)] at heq
          linarith
      · -- Case x < 1
        by_cases h4 : x ≥ -2
        · -- Case -2 ≤ x < 1
          by_cases h2 : y ≥ 5
          · -- Case y ≥ 5
            rw [abs_of_nonneg (show x + 2 ≥ 0 by linarith), abs_of_nonneg (show 1 - x ≥ 0 by linarith)] at heq
            rw [abs_of_nonneg (show y - 5 ≥ 0 by linarith), abs_of_nonneg (show 1 + y ≥ 0 by linarith)] at heq
            linarith
          by_cases h3 : y ≤ -1
          · -- Case y ≤ -1
            rw [abs_of_nonneg (show x + 2 ≥ 0 by linarith), abs_of_nonneg (show 1 - x ≥ 0 by linarith)] at heq
            rw [abs_of_nonpos (show y - 5 ≤ 0 by linarith), abs_of_nonpos (show 1 + y ≤ 0 by linarith)] at heq
            linarith
          · -- Case -1 < y < 5
            rw [abs_of_nonneg (show x + 2 ≥ 0 by linarith), abs_of_nonneg (show 1 - x ≥ 0 by linarith)] at heq
            rw [abs_of_nonpos (show y - 5 ≤ 0 by linarith), abs_of_nonneg (show 1 + y ≥ 0 by linarith)] at heq
            linarith
        · -- Case x < -2
          by_cases h6 : y ≥ 5
          · -- Case y ≥ 5
            rw [abs_of_nonpos (show x + 2 ≤ 0 by linarith), abs_of_nonneg (show 1 - x ≥ 0 by linarith)] at heq
            rw [abs_of_nonneg (show y - 5 ≥ 0 by linarith), abs_of_nonneg (show 1 + y ≥ 0 by linarith)] at heq
            linarith
          by_cases h7 : y ≤ -1
          · -- Case y ≤ -1
            rw [abs_of_nonpos (show x + 2 ≤ 0 by linarith), abs_of_nonneg (show 1 - x ≥ 0 by linarith)] at heq
            rw [abs_of_nonpos (show y - 5 ≤ 0 by linarith), abs_of_nonpos (show 1 + y ≤ 0 by linarith)] at heq
            linarith
          · -- Case -1 < y < 5
            rw [abs_of_nonpos (show x + 2 ≤ 0 by linarith), abs_of_nonneg (show 1 - x ≥ 0 by linarith)] at heq
            rw [abs_of_nonpos (show y - 5 ≤ 0 by linarith), abs_of_nonneg (show 1 + y ≥ 0 by linarith)] at heq
            linarith