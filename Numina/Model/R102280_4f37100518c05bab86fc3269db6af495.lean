import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_267990 :
  IsLeast {y : ℝ | ∃ x, y = |2 * x - 1| + |3 * x - 2| + |4 * x - 3| + |5 * x - 4|} 1 := by
  constructor
  · -- Show that 1 is in the set
    use (3 / 4)
    norm_num [abs_of_nonneg, abs_of_nonpos]
    all_goals norm_num
  · -- Show that 1 is a lower bound
    intro y hy
    rcases hy with ⟨x, hx⟩
    have h1 : |2 * x - 1| + |3 * x - 2| + |4 * x - 3| + |5 * x - 4| ≥ 1 := by
      by_cases h1 : 2 * x - 1 ≥ 0
      · -- Case where |2x-1| = 2x-1
        rw [abs_of_nonneg h1]
        by_cases h2 : 3 * x - 2 ≥ 0
        · -- Case where |3x-2| = 3x-2
          rw [abs_of_nonneg h2]
          by_cases h3 : 4 * x - 3 ≥ 0
          · -- Case where |4x-3| = 4x-3
            rw [abs_of_nonneg h3]
            by_cases h4 : 5 * x - 4 ≥ 0
            · -- Case where |5x-4| = 5x-4
              rw [abs_of_nonneg h4]
              linarith
            · -- Case where |5x-4| = 4-5x
              rw [abs_of_neg (lt_of_not_ge h4)]
              linarith
          · -- Case where |4x-3| = 3-4x
            rw [abs_of_neg (lt_of_not_ge h3)]
            by_cases h4 : 5 * x - 4 ≥ 0
            · -- Case where |5x-4| = 5x-4
              rw [abs_of_nonneg h4]
              linarith
            · -- Case where |5x-4| = 4-5x
              rw [abs_of_neg (lt_of_not_ge h4)]
              linarith
        · -- Case where |3x-2| = 2-3x
          rw [abs_of_neg (lt_of_not_ge h2)]
          by_cases h3 : 4 * x - 3 ≥ 0
          · -- Case where |4x-3| = 4x-3
            rw [abs_of_nonneg h3]
            by_cases h4 : 5 * x - 4 ≥ 0
            · -- Case where |5x-4| = 5x-4
              rw [abs_of_nonneg h4]
              linarith
            · -- Case where |5x-4| = 4-5x
              rw [abs_of_neg (lt_of_not_ge h4)]
              linarith
          · -- Case where |4x-3| = 3-4x
            rw [abs_of_neg (lt_of_not_ge h3)]
            by_cases h4 : 5 * x - 4 ≥ 0
            · -- Case where |5x-4| = 5x-4
              rw [abs_of_nonneg h4]
              linarith
            · -- Case where |5x-4| = 4-5x
              rw [abs_of_neg (lt_of_not_ge h4)]
              linarith
      · -- Case where |2x-1| = 1-2x
        rw [abs_of_neg (lt_of_not_ge h1)]
        by_cases h2 : 3 * x - 2 ≥ 0
        · -- Case where |3x-2| = 3x-2
          rw [abs_of_nonneg h2]
          by_cases h3 : 4 * x - 3 ≥ 0
          · -- Case where |4x-3| = 4x-3
            rw [abs_of_nonneg h3]
            by_cases h4 : 5 * x - 4 ≥ 0
            · -- Case where |5x-4| = 5x-4
              rw [abs_of_nonneg h4]
              linarith
            · -- Case where |5x-4| = 4-5x
              rw [abs_of_neg (lt_of_not_ge h4)]
              linarith
          · -- Case where |4x-3| = 3-4x
            rw [abs_of_neg (lt_of_not_ge h3)]
            by_cases h4 : 5 * x - 4 ≥ 0
            · -- Case where |5x-4| = 5x-4
              rw [abs_of_nonneg h4]
              linarith
            · -- Case where |5x-4| = 4-5x
              rw [abs_of_neg (lt_of_not_ge h4)]
              linarith
        · -- Case where |3x-2| = 2-3x
          rw [abs_of_neg (lt_of_not_ge h2)]
          by_cases h3 : 4 * x - 3 ≥ 0
          · -- Case where |4x-3| = 4x-3
            rw [abs_of_nonneg h3]
            by_cases h4 : 5 * x - 4 ≥ 0
            · -- Case where |5x-4| = 5x-4
              rw [abs_of_nonneg h4]
              linarith
            · -- Case where |5x-4| = 4-5x
              rw [abs_of_neg (lt_of_not_ge h4)]
              linarith
          · -- Case where |4x-3| = 3-4x
            rw [abs_of_neg (lt_of_not_ge h3)]
            by_cases h4 : 5 * x - 4 ≥ 0
            · -- Case where |5x-4| = 5x-4
              rw [abs_of_nonneg h4]
              linarith
            · -- Case where |5x-4| = 4-5x
              rw [abs_of_neg (lt_of_not_ge h4)]
              linarith
    linarith [show y = |2 * x - 1| + |3 * x - 2| + |4 * x - 3| + |5 * x - 4| from by linarith [hx], h1]