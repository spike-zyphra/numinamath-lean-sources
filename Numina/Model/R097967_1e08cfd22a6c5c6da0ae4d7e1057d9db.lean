import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_298153 :
  IsLeast {y : ℝ | ∃ x, y = abs (2 * x - 1) + abs (3 * x - 2) + abs (4 * x - 3) + abs (5 * x - 4)} 1 := by
  constructor
  · -- Show that 1 is achievable
    use 3 / 4
    norm_num [abs]
  · -- Show that 1 is the least
    intro y hy
    rcases hy with ⟨x, hx⟩
    have h1 : abs (2 * x - 1) + abs (3 * x - 2) + abs (4 * x - 3) + abs (5 * x - 4) ≥ 1 := by
      by_cases h1 : 2 * x - 1 ≥ 0
      · -- Case where 2x - 1 >= 0
        rw [abs_of_nonneg h1]
        by_cases h2 : 3 * x - 2 ≥ 0
        · -- Case where 3x - 2 >= 0
          rw [abs_of_nonneg h2]
          by_cases h3 : 4 * x - 3 ≥ 0
          · -- Case where 4x - 3 >= 0
            rw [abs_of_nonneg h3]
            by_cases h4 : 5 * x - 4 ≥ 0
            · -- Case where 5x - 4 >= 0
              rw [abs_of_nonneg h4]
              linarith
            · -- Case where 5x - 4 < 0
              rw [abs_of_neg (lt_of_not_ge h4)]
              linarith
          · -- Case where 4x - 3 < 0
            rw [abs_of_neg (lt_of_not_ge h3)]
            by_cases h4 : 5 * x - 4 ≥ 0
            · -- Case where 5x - 4 >= 0
              rw [abs_of_nonneg h4]
              linarith
            · -- Case where 5x - 4 < 0
              rw [abs_of_neg (lt_of_not_ge h4)]
              linarith
        · -- Case where 3x - 2 < 0
          rw [abs_of_neg (lt_of_not_ge h2)]
          by_cases h3 : 4 * x - 3 ≥ 0
          · -- Case where 4x - 3 >= 0
            rw [abs_of_nonneg h3]
            by_cases h4 : 5 * x - 4 ≥ 0
            · -- Case where 5x - 4 >= 0
              rw [abs_of_nonneg h4]
              linarith
            · -- Case where 5x - 4 < 0
              rw [abs_of_neg (lt_of_not_ge h4)]
              linarith
          · -- Case where 4x - 3 < 0
            rw [abs_of_neg (lt_of_not_ge h3)]
            by_cases h4 : 5 * x - 4 ≥ 0
            · -- Case where 5x - 4 >= 0
              rw [abs_of_nonneg h4]
              linarith
            · -- Case where 5x - 4 < 0
              rw [abs_of_neg (lt_of_not_ge h4)]
              linarith
      · -- Case where 2x - 1 < 0
        rw [abs_of_neg (lt_of_not_ge h1)]
        by_cases h2 : 3 * x - 2 ≥ 0
        · -- Case where 3x - 2 >= 0
          rw [abs_of_nonneg h2]
          by_cases h3 : 4 * x - 3 ≥ 0
          · -- Case where 4x - 3 >= 0
            rw [abs_of_nonneg h3]
            by_cases h4 : 5 * x - 4 ≥ 0
            · -- Case where 5x - 4 >= 0
              rw [abs_of_nonneg h4]
              linarith
            · -- Case where 5x - 4 < 0
              rw [abs_of_neg (lt_of_not_ge h4)]
              linarith
          · -- Case where 4x - 3 < 0
            rw [abs_of_neg (lt_of_not_ge h3)]
            by_cases h4 : 5 * x - 4 ≥ 0
            · -- Case where 5x - 4 >= 0
              rw [abs_of_nonneg h4]
              linarith
            · -- Case where 5x - 4 < 0
              rw [abs_of_neg (lt_of_not_ge h4)]
              linarith
        · -- Case where 3x - 2 < 0
          rw [abs_of_neg (lt_of_not_ge h2)]
          by_cases h3 : 4 * x - 3 ≥ 0
          · -- Case where 4x - 3 >= 0
            rw [abs_of_nonneg h3]
            by_cases h4 : 5 * x - 4 ≥ 0
            · -- Case where 5x - 4 >= 0
              rw [abs_of_nonneg h4]
              linarith
            · -- Case where 5x - 4 < 0
              rw [abs_of_neg (lt_of_not_ge h4)]
              linarith
          · -- Case where 4x - 3 < 0
            rw [abs_of_neg (lt_of_not_ge h3)]
            by_cases h4 : 5 * x - 4 ≥ 0
            · -- Case where 5x - 4 >= 0
              rw [abs_of_nonneg h4]
              linarith
            · -- Case where 5x - 4 < 0
              rw [abs_of_neg (lt_of_not_ge h4)]
              linarith
    linarith [abs_nonneg (2 * x - 1), abs_nonneg (3 * x - 2), abs_nonneg (4 * x - 3), abs_nonneg (5 * x - 4)]