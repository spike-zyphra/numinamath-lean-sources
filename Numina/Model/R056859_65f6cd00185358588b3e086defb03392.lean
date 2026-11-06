import Mathlib

theorem algebra_1013 :
  IsLeast {n : ℝ | ∃ x : ℝ, n = abs (x + 1) + abs (x + 2) + abs (x + 3) + abs (x + 4)} 4 := by
  constructor
  · -- First, prove that 4 is achievable, so it exists in the set
    use (-3)
    norm_num [abs_of_nonneg, abs_of_nonpos]
    all_goals norm_num
  · -- Then, prove that 4 is the smallest
    intro n hn
    rcases hn with ⟨x, hx⟩
    -- Now we have to show that n >= 4
    rw [hx] at *
    have h1 : abs (x + 1) + abs (x + 2) + abs (x + 3) + abs (x + 4) ≥ 4 := by
      by_cases h1 : x + 1 ≥ 0
      · by_cases h2 : x + 2 ≥ 0
        · by_cases h3 : x + 3 ≥ 0
          · by_cases h4 : x + 4 ≥ 0
            · -- Case x >= -1: All terms non-negative
              rw [abs_of_nonneg h1, abs_of_nonneg h2, abs_of_nonneg h3, abs_of_nonneg h4]
              linarith
            · -- Case -2 <= x < -1: |x + 1| neg, others non-negative
              rw [abs_of_nonneg h1, abs_of_nonneg h2, abs_of_nonneg h3, abs_of_neg (not_le.mp h4)]
              linarith
          · by_cases h4 : x + 4 >= 0
            · -- Case -3 <= x < -2: |x + 1|, |x + 2| neg, others non-negative
              rw [abs_of_nonneg h1, abs_of_nonneg h2, abs_of_neg (not_le.mp h3), abs_of_nonneg h4]
              linarith
            · -- Case -4 <= x < -3: |x + 1|, |x + 2|, |x + 3| neg, |x + 4| non-negative
              rw [abs_of_nonneg h1, abs_of_nonneg h2, abs_of_neg (not_le.mp h3), abs_of_neg (not_le.mp h4)]
              linarith
        · by_cases h3 : x + 3 >= 0
          · by_cases h4 : x + 4 >= 0
            · -- Case -2 <= x < -1: |x + 1| neg, others non-negative
              rw [abs_of_nonneg h1, abs_of_neg (not_le.mp h2), abs_of_nonneg h3, abs_of_nonneg h4]
              linarith
            · -- Case -2 <= x < -1: |x + 1| neg, others non-negative
              rw [abs_of_nonneg h1, abs_of_neg (not_le.mp h2), abs_of_nonneg h3, abs_of_neg (not_le.mp h4)]
              linarith
          · by_cases h4 : x + 4 >= 0
            · -- Case -3 <= x < -2: |x + 1|, |x + 2| neg, others non-negative
              rw [abs_of_nonneg h1, abs_of_neg (not_le.mp h2), abs_of_neg (not_le.mp h3), abs_of_nonneg h4]
              linarith
            · -- Case -4 <= x < -3: |x + 1|, |x + 2|, |x + 3| neg, |x + 4| non-negative
              rw [abs_of_nonneg h1, abs_of_neg (not_le.mp h2), abs_of_neg (not_le.mp h3), abs_of_neg (not_le.mp h4)]
              linarith
      · by_cases h2 : x + 2 >= 0
        · by_cases h3 : x + 3 >= 0
          · by_cases h4 : x + 4 >= 0
            · -- Case -2 <= x < -1: |x + 1| neg, others non-negative
              rw [abs_of_neg (not_le.mp h1), abs_of_nonneg h2, abs_of_nonneg h3, abs_of_nonneg h4]
              linarith
            · -- Case -2 <= x < -1: |x + 1| neg, others non-negative
              rw [abs_of_neg (not_le.mp h1), abs_of_nonneg h2, abs_of_nonneg h3, abs_of_neg (not_le.mp h4)]
              linarith
          · by_cases h4 : x + 4 >= 0
            · -- Case -3 <= x < -2: |x + 1|, |x + 2| neg, others non-negative
              rw [abs_of_neg (not_le.mp h1), abs_of_nonneg h2, abs_of_neg (not_le.mp h3), abs_of_nonneg h4]
              linarith
            · -- Case -4 <= x < -3: |x + 1|, |x + 2|, |x + 3| neg, |x + 4| non-negative
              rw [abs_of_neg (not_le.mp h1), abs_of_nonneg h2, abs_of_neg (not_le.mp h3), abs_of_neg (not_le.mp h4)]
              linarith
        · by_cases h3 : x + 3 >= 0
          · by_cases h4 : x + 4 >= 0
            · -- Case -3 <= x < -2: |x + 1|, |x + 2| neg, others non-negative
              rw [abs_of_neg (not_le.mp h1), abs_of_neg (not_le.mp h2), abs_of_nonneg h3, abs_of_nonneg h4]
              linarith
            · -- Case -3 <= x < -2: |x + 1|, |x + 2| neg, others non-negative
              rw [abs_of_neg (not_le.mp h1), abs_of_neg (not_le.mp h2), abs_of_nonneg h3, abs_of_neg (not_le.mp h4)]
              linarith
          · by_cases h4 : x + 4 >= 0
            · -- Case -4 <= x < -3: |x + 1|, |x + 2|, |x + 3| neg, |x + 4| non-negative
              rw [abs_of_neg (not_le.mp h1), abs_of_neg (not_le.mp h2), abs_of_neg (not_le.mp h3), abs_of_nonneg h4]
              linarith
            · -- Case x < -4: All terms negative
              rw [abs_of_neg (not_le.mp h1), abs_of_neg (not_le.mp h2), abs_of_neg (not_le.mp h3), abs_of_neg (not_le.mp h4)]
              linarith
    linarith