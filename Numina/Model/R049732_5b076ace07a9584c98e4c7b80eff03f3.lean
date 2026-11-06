import Mathlib

theorem algebra_296822 (x : ℝ) :
    abs (x + 1) + abs (x + 2) + abs (x - 5) = 10 ↔
    x = -8 / 3 ∨ x = 2 := by
  constructor
  · -- Forward direction: if the equation holds, then x is either -8/3 or 2
    intro h
    by_cases h1 : x ≥ 5
    · -- Case x ≥ 5
      rw [abs_of_nonneg (show x + 1 ≥ 0 by linarith), 
          abs_of_nonneg (show x + 2 ≥ 0 by linarith), 
          abs_of_nonneg (show x - 5 ≥ 0 by linarith)] at h
      have h4 : x = 4 := by
        linarith
      linarith
    · -- Case -1 ≤ x < 5
      by_cases h2 : x ≥ -1
      · -- Case -1 ≤ x < 5
        rw [abs_of_nonneg (show x + 1 ≥ 0 by linarith), 
            abs_of_nonneg (show x + 2 ≥ 0 by linarith), 
            abs_of_neg (show x - 5 < 0 by linarith)] at h
        have h5 : x = 2 := by
          linarith
        right
        exact h5
      · -- Case -2 ≤ x < -1
        by_cases h3 : x ≥ -2
        · -- Case -2 ≤ x < -1
          rw [abs_of_neg (show x + 1 < 0 by linarith), 
              abs_of_nonneg (show x + 2 ≥ 0 by linarith), 
              abs_of_neg (show x - 5 < 0 by linarith)] at h
          exfalso
          linarith
        · -- Case x < -2
          rw [abs_of_neg (show x + 1 < 0 by linarith), 
              abs_of_neg (show x + 2 < 0 by linarith), 
              abs_of_neg (show x - 5 < 0 by linarith)] at h
          have h6 : x = -8 / 3 := by
            linarith
          left
          exact h6
  · -- Backward direction: if x is either -8/3 or 2, then the equation holds
    rintro (h | h)
    · -- Case x = -8/3
      rw [h]
      norm_num [abs_of_nonneg, abs_of_neg]
    · -- Case x = 2
      rw [h]
      norm_num [abs_of_nonneg, abs_of_neg]