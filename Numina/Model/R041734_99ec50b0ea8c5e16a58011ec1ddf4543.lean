import Mathlib

theorem algebra_212692 (x : ℝ) :
    abs (x + 1) - abs x + 3 * abs (x - 1) - 2 * abs (x - 2) = x + 2 ↔
    x = -2 ∨ x ≥ 2 := by
  constructor
  · -- Assume the equation holds, prove x = -2 or x >= 2
    intro h
    by_cases h1 : x < -1
    · -- Case 1: x < -1
      rw [abs_of_neg (show x + 1 < 0 by linarith), 
          abs_of_neg (show x < 0 by linarith), 
          abs_of_neg (show x - 1 < 0 by linarith), 
          abs_of_neg (show x - 2 < 0 by linarith)
          ] at h
      left
      linarith
    · -- Case 2: -1 ≤ x < 0
      by_cases h2 : x < 0
      · -- Subcase 2a: -1 ≤ x < 0
        rw [abs_of_nonneg (show x + 1 ≥ 0 by linarith), 
            abs_of_neg (show x < 0 by linarith), 
            abs_of_neg (show x - 1 < 0 by linarith), 
            abs_of_neg (show x - 2 < 0 by linarith)
            ] at h
        exfalso
        linarith
      · -- Case 2b: 0 ≤ x < 1
        by_cases h3 : x < 1
        · -- Subcase 2b1: 0 ≤ x < 1
          rw [abs_of_nonneg (show x + 1 ≥ 0 by linarith), 
              abs_of_nonneg (show x ≥ 0 by linarith), 
              abs_of_neg (show x - 1 < 0 by linarith), 
              abs_of_neg (show x - 2 < 0 by linarith)
              ] at h
          exfalso
          linarith
        · -- Case 2b2: 1 ≤ x < 2
          by_cases h4 : x < 2
          · -- Subcase 2b2a: 1 ≤ x < 2
            rw [abs_of_nonneg (show x + 1 ≥ 0 by linarith), 
                abs_of_nonneg (show x ≥ 0 by linarith), 
                abs_of_nonneg (show x - 1 ≥ 0 by linarith), 
                abs_of_neg (show x - 2 < 0 by linarith)
                ] at h
            exfalso
            linarith
          · -- Case 2b2b: x ≥ 2
            rw [abs_of_nonneg (show x + 1 ≥ 0 by linarith), 
                abs_of_nonneg (show x ≥ 0 by linarith), 
                abs_of_nonneg (show x - 1 ≥ 0 by linarith), 
                abs_of_nonneg (show x - 2 ≥ 0 by linarith)
                ] at h
            right
            linarith
  · -- Assume x = -2 or x >= 2, prove the equation
    rintro (h | h)
    · -- Case 1: x = -2
      rw [h]
      norm_num [abs_of_nonneg, abs_of_nonpos]
    · -- Case 2: x >= 2
      rw [abs_of_nonneg (show x + 1 ≥ 0 by linarith), 
          abs_of_nonneg (show x ≥ 0 by linarith), 
          abs_of_nonneg (show x - 1 ≥ 0 by linarith), 
          abs_of_nonneg (show x - 2 ≥ 0 by linarith)
          ]
      linarith