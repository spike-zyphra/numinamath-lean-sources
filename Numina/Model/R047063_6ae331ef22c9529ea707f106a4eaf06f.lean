import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_194018 :
  IsLeast {x | ∃ a : ℝ, x = ∑ i ∈ Finset.range 10, |a - (i + 1)|} 25 := by
  constructor
  · -- Show 25 is in the set.
    use 5
    norm_num [Finset.sum_range_succ]
    <;> norm_num [abs]
  · -- Show that 25 is the minimum element.
    intro x hx
    rcases hx with ⟨a, ha⟩
    have h1 : x = ∑ i in Finset.range 10, |a - (i + 1)| := by
      simpa using ha
    have h2 : x ≥ 25 := by
      have h3 : ∑ i in Finset.range 10, |a - (i + 1)| ≥ 25 := by
        norm_num [Finset.sum_range_succ]
        by_cases h1 : a ≥ 10
        · -- Case where a ≥ 10
          rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
          nlinarith
        by_cases h2 : a ≥ 9
        · -- Case where 9 ≤ a < 10
          rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_neg (by linarith)]
          nlinarith
        by_cases h3 : a ≥ 8
        · -- Case where 8 ≤ a < 9
          rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_neg (by linarith), abs_of_neg (by linarith)]
          nlinarith
        by_cases h4 : a ≥ 7
        · -- Case where 7 ≤ a < 8
          rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_neg (by linarith), abs_of_neg (by linarith), abs_of_neg (by linarith)]
          nlinarith
        by_cases h5 : a ≥ 6
        · -- Case where 6 ≤ a < 7
          rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_neg (by linarith), abs_of_neg (by linarith), abs_of_neg (by linarith), abs_of_neg (by linarith)]
          nlinarith
        by_cases h6 : a ≥ 5
        · -- Case where 5 ≤ a < 6
          rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_neg (by linarith), abs_of_neg (by linarith), abs_of_neg (by linarith), abs_of_neg (by linarith), abs_of_neg (by linarith)]
          nlinarith
        by_cases h7 : a ≥ 4
        · -- Case where 4 ≤ a < 5
          rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_neg (by linarith), abs_of_neg (by linarith), abs_of_neg (by linarith), abs_of_neg (by linarith), abs_of_neg (by linarith), abs_of_neg (by linarith)]
          nlinarith
        by_cases h8 : a ≥ 3
        · -- Case where 3 ≤ a < 4
          rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_neg (by linarith), abs_of_neg (by linarith), abs_of_neg (by linarith), abs_of_neg (by linarith), abs_of_neg (by linarith), abs_of_neg (by linarith), abs_of_neg (by linarith)]
          nlinarith
        by_cases h9 : a ≥ 2
        · -- Case where 2 ≤ a < 3
          rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_neg (by linarith), abs_of_neg (by linarith), abs_of_neg (by linarith), abs_of_neg (by linarith), abs_of_neg (by linarith), abs_of_neg (by linarith), abs_of_neg (by linarith), abs_of_neg (by linarith)]
          nlinarith
        by_cases h10 : a ≥ 1
        · -- Case where 1 ≤ a < 2
          rw [abs_of_nonneg (by linarith), abs_of_neg (by linarith), abs_of_neg (by linarith), abs_of_neg (by linarith), abs_of_neg (by linarith), abs_of_neg (by linarith), abs_of_neg (by linarith), abs_of_neg (by linarith), abs_of_neg (by linarith), abs_of_neg (by linarith)]
          nlinarith
        · -- Case where a < 1
          rw [abs_of_neg (by linarith), abs_of_neg (by linarith), abs_of_neg (by linarith), abs_of_neg (by linarith), abs_of_neg (by linarith), abs_of_neg (by linarith), abs_of_neg (by linarith), abs_of_neg (by linarith), abs_of_neg (by linarith), abs_of_neg (by linarith)]
          nlinarith
      linarith
    linarith [h1, h2]