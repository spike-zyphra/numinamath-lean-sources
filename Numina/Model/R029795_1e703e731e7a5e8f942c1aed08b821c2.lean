import Mathlib

open Real Set

theorem algebra_200682 :
    IsLeast {x | ∃ t : ℝ, x = abs (2 * t - 1) + abs (3 * t - 2) + abs (4 * t - 3) + abs (5 * t - 4)} 1 := by
  constructor
  · -- Show 1 is in the set
    use (3 / 4)
    norm_num [abs_of_nonneg, abs_of_nonpos]
    all_goals norm_num [abs_of_nonneg, abs_of_nonpos]

  · -- Show there is no smaller element in the set
    intro x hx
    rcases hx with ⟨t, ht⟩
    have h1 : abs (2 * t - 1) + abs (3 * t - 2) + abs (4 * t - 3) + abs (5 * t - 4) ≥ 1 := by
      by_cases h1 : 2 * t - 1 ≥ 0
      · -- Case 1: 2*t - 1 ≥ 0
        rw [abs_of_nonneg h1]
        by_cases h2 : 3 * t - 2 ≥ 0
        · -- Case 1a: 3*t - 2 ≥ 0
          rw [abs_of_nonneg h2]
          by_cases h3 : 4 * t - 3 ≥ 0
          · -- Case 1a1: 4*t - 3 ≥ 0
            rw [abs_of_nonneg h3]
            by_cases h4 : 5 * t - 4 ≥ 0
            · -- Case 1a1a: 5*t - 4 ≥ 0
              rw [abs_of_nonneg h4]
              linarith
            · -- Case 1a1b: 5*t - 4 < 0
              rw [abs_of_neg (not_le.mp h4)]
              linarith
          · -- Case 1a2: 4*t - 3 < 0
            rw [abs_of_neg (not_le.mp h3)]
            by_cases h4 : 5 * t - 4 ≥ 0
            · -- Case 1a2a: 5*t - 4 ≥ 0
              rw [abs_of_nonneg h4]
              linarith
            · -- Case 1a2b: 5*t - 4 < 0
              rw [abs_of_neg (not_le.mp h4)]
              linarith
        · -- Case 1b: 3*t - 2 < 0
          rw [abs_of_neg (not_le.mp h2)]
          by_cases h3 : 4 * t - 3 ≥ 0
          · -- Case 1b1: 4*t - 3 ≥ 0
            rw [abs_of_nonneg h3]
            by_cases h4 : 5 * t - 4 ≥ 0
            · -- Case 1b1a: 5*t - 4 ≥ 0
              rw [abs_of_nonneg h4]
              linarith
            · -- Case 1b1b: 5*t - 4 < 0
              rw [abs_of_neg (not_le.mp h4)]
              linarith
          · -- Case 1b2: 4*t - 3 < 0
            rw [abs_of_neg (not_le.mp h3)]
            by_cases h4 : 5 * t - 4 ≥ 0
            · -- 1b2a
              rw [abs_of_nonneg h4]
              linarith
            · -- 1b2b
              rw [abs_of_neg (not_le.mp h4)]
              linarith
      · -- Case 2: 2*t - 1 < 0
        rw [abs_of_neg (not_le.mp h1)]
        by_cases h2 : 3 * t - 2 ≥ 0
        · -- Case 2a: 3*t - 2 ≥ 0
          rw [abs_of_nonneg h2]
          by_cases h3 : 4 * t - 3 ≥ 0
          · -- Case 2a1: 4*t - 3 ≥ 0
            rw [abs_of_nonneg h3]
            by_cases h4 : 5 * t - 4 ≥ 0
            · -- 2a1a
              rw [abs_of_nonneg h4]
              linarith
            · -- 2a1b
              rw [abs_of_neg (not_le.mp h4)]
              linarith
          · -- Case 2a2: 4*t - 3 < 0
            rw [abs_of_neg (not_le.mp h3)]
            by_cases h4 : 5 * t - 4 ≥ 0
            · -- 2a2a
              rw [abs_of_nonneg h4]
              linarith
            · -- 2a2b
              rw [abs_of_neg (not_le.mp h4)]
              linarith
        · -- Case 2b: 3*t - 2 < 0
          rw [abs_of_neg (not_le.mp h2)]
          by_cases h3 : 4 * t - 3 ≥ 0
          · -- Case 2b1: 4*t - 3 ≥ 0
            rw [abs_of_nonneg h3]
            by_cases h4 : 5 * t - 4 ≥ 0
            · -- 2b1a
              rw [abs_of_nonneg h4]
              linarith
            · -- 2b1b
              rw [abs_of_neg (not_le.mp h4)]
              linarith
          · -- Case 2b2: 4*t - 3 < 0
            rw [abs_of_neg (not_le.mp h3)]
            by_cases h4 : 5 * t - 4 ≥ 0
            · -- 2b2a
              rw [abs_of_nonneg h4]
              linarith
            · -- 2b2b
              rw [abs_of_neg (not_le.mp h4)]
              linarith
    linarith [ht, h1]