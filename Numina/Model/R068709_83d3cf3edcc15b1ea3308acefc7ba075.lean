import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_59063 :
  IsGreatest {x | ∃ y : ℝ, x = 1 / (abs (y + 1) + abs (y + 2) + abs (y - 3))} (1 / 5) := by
  constructor
  · -- Show that 1/5 is attainable
    use -1
    norm_num [abs_of_nonneg, abs_of_nonpos]
    all_goals norm_num
  · -- Show that 1/5 is the greatest value
    intro x h
    rcases h with ⟨y, hy⟩
    have h1 : abs (y + 1) + abs (y + 2) + abs (y - 3) ≥ 5 := by
      by_cases h1 : y + 1 ≥ 0
      · -- This simplifies to y >= -1
        by_cases h2 : y + 2 ≥ 0
        · -- This simplifies to y >= -2
          by_cases h3 : y - 3 ≥ 0
          · -- This simplifies to y >= 3
            rw [abs_of_nonneg h1, abs_of_nonneg h2, abs_of_nonneg h3]
            linarith
          · -- Case where y + 1 >= 0, y + 2 >= 0, y - 3 < 0
            rw [abs_of_nonneg h1, abs_of_nonneg h2, abs_of_neg (lt_of_not_ge h3)]
            linarith
        · -- Case where y + 1 >= 0, y + 2 < 0
          by_cases h3 : y - 3 ≥ 0
          · -- Case where y + 1 >= 0, y + 2 < 0, y - 3 >= 0
            rw [abs_of_nonneg h1, abs_of_neg (lt_of_not_ge h2), abs_of_nonneg h3]
            linarith
          · -- Case where y + 1 >= 0, y + 2 < 0, y - 3 < 0
            rw [abs_of_nonneg h1, abs_of_neg (lt_of_not_ge h2), abs_of_neg (lt_of_not_ge h3)]
            linarith
      · -- Case where y + 1 < 0
        by_cases h2 : y + 2 ≥ 0
        · -- Case where y + 1 < 0, y + 2 >= 0
          by_cases h3 : y - 3 ≥ 0
          · -- Case where y + 1 < 0, y + 2 >= 0, y - 3 >= 0
            rw [abs_of_neg (lt_of_not_ge h1), abs_of_nonneg h2, abs_of_nonneg h3]
            linarith
          · -- Case where y + 1 < 0, y + 2 >= 0, y - 3 < 0
            rw [abs_of_neg (lt_of_not_ge h1), abs_of_nonneg h2, abs_of_neg (lt_of_not_ge h3)]
            linarith
        · -- Case where y + 1 < 0, y + 2 < 0
          by_cases h3 : y - 3 ≥ 0
          · -- Case where y + 1 < 0, y + 2 < 0, y - 3 >= 0
            rw [abs_of_neg (lt_of_not_ge h1), abs_of_neg (lt_of_not_ge h2), abs_of_nonneg h3]
            linarith
          · -- Case where y + 1 < 0, y + 2 < 0, y - 3 < 0
            rw [abs_of_neg (lt_of_not_ge h1), abs_of_neg (lt_of_not_ge h2), abs_of_neg (lt_of_not_ge h3)]
            linarith
    have h2 : 1 / (abs (y + 1) + abs (y + 2) + abs (y - 3)) ≤ 1 / 5 := by
      apply one_div_le_one_div_of_le
      positivity
      linarith
    rw [hy] at *
    linarith