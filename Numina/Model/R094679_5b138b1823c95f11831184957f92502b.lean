import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_219628 :
  IsLeast {x | ∃ a : ℝ, x = abs (2*a-1) + abs (3*a-2) + abs (4*a-3) + abs (5*a-4)} 1 := by
  constructor
  · -- We will show that 1 is achievable by finding a specific value of a
    use 3 / 4
    norm_num [abs_of_nonneg, abs_of_nonpos]
    all_goals norm_num
  · -- Now we need to show that 1 is the minimum
    intro x hx
    rcases hx with ⟨a, ha⟩
    have h1 : abs (2 * a - 1) + abs (3 * a - 2) + abs (4 * a - 3) + abs (5 * a - 4) ≥ 1 := by
      by_cases h1 : 2 * a - 1 ≥ 0
      · -- Case where 2a - 1 ≥ 0
        rw [abs_of_nonneg h1]
        by_cases h2 : 3 * a - 2 ≥ 0
        · -- Case where 3a - 2 ≥ 0
          rw [abs_of_nonneg h2]
          by_cases h3 : 4 * a - 3 ≥ 0
          · -- Case where 4a - 3 ≥ 0
            rw [abs_of_nonneg h3]
            by_cases h4 : 5 * a - 4 ≥ 0
            · -- Case where 5a - 4 ≥ 0
              rw [abs_of_nonneg h4]
              linarith
            · -- Case where 5a - 4 < 0
              rw [abs_of_neg (lt_of_not_ge h4)]
              linarith
          · -- Case where 4a - 3 < 0
            rw [abs_of_neg (lt_of_not_ge h3)]
            by_cases h4 : 5 * a - 4 ≥ 0
            · -- Case where 5a - 4 ≥ 0
              rw [abs_of_nonneg h4]
              linarith
            · -- Case where 5a - 4 < 0
              rw [abs_of_neg (lt_of_not_ge h4)]
              linarith
        · -- Case where 3a - 2 < 0
          rw [abs_of_neg (lt_of_not_ge h2)]
          by_cases h3 : 4 * a - 3 ≥ 0
          · -- Case where 4a - 3 ≥ 0
            rw [abs_of_nonneg h3]
            by_cases h4 : 5 * a - 4 ≥ 0
            · -- Case where 5a - 4 ≥ 0
              rw [abs_of_nonneg h4]
              linarith
            · -- Case where 5a - 4 < 0
              rw [abs_of_neg (lt_of_not_ge h4)]
              linarith
          · -- Case where 4a - 3 < 0
            rw [abs_of_neg (lt_of_not_ge h3)]
            by_cases h4 : 5 * a - 4 ≥ 0
            · -- Case where 5a - 4 ≥ 0
              rw [abs_of_nonneg h4]
              linarith
            · -- Case where 5a - 4 < 0
              rw [abs_of_neg (lt_of_not_ge h4)]
              linarith
      · -- Case where 2a - 1 < 0
        rw [abs_of_neg (lt_of_not_ge h1)]
        by_cases h2 : 3 * a - 2 ≥ 0
        · -- Case where 3a - 2 ≥ 0
          rw [abs_of_nonneg h2]
          by_cases h3 : 4 * a - 3 ≥ 0
          · -- Case where 4a - 3 ≥ 0
            rw [abs_of_nonneg h3]
            by_cases h4 : 5 * a - 4 ≥ 0
            · -- Case where 5a - 4 ≥ 0
              rw [abs_of_nonneg h4]
              linarith
            · -- Case where 5a - 4 < 0
              rw [abs_of_neg (lt_of_not_ge h4)]
              linarith
          · -- Case where 4a - 3 < 0
            rw [abs_of_neg (lt_of_not_ge h3)]
            by_cases h4 : 5 * a - 4 ≥ 0
            · -- Case where 5a - 4 ≥ 0
              rw [abs_of_nonneg h4]
              linarith
            · -- Case where 5a - 4 < 0
              rw [abs_of_neg (lt_of_not_ge h4)]
              linarith
        · -- Case where 3a - 2 < 0
          rw [abs_of_neg (lt_of_not_ge h2)]
          by_cases h3 : 4 * a - 3 ≥ 0
          · -- Case where 4a - 3 ≥ 0
            rw [abs_of_nonneg h3]
            by_cases h4 : 5 * a - 4 ≥ 0
            · -- Case where 5a - 4 ≥ 0
              rw [abs_of_nonneg h4]
              linarith
            · -- Case where 5a - 4 < 0
              rw [abs_of_neg (lt_of_not_ge h4)]
              linarith
          · -- Case where 4a - 3 < 0
            rw [abs_of_neg (lt_of_not_ge h3)]
            by_cases h4 : 5 * a - 4 ≥ 0
            · -- Case where 5a - 4 ≥ 0
              rw [abs_of_nonneg h4]
              linarith
            · -- Case where 5a - 4 < 0
              rw [abs_of_neg (lt_of_not_ge h4)]
              linarith
    linarith [h1, ha]