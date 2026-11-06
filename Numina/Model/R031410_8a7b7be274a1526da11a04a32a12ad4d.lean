import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_150167 :
  IsLeast {x | ∃ a : ℝ, x = ∑ i : Fin 10, |a - (i + 1)|} 25 := by
  constructor
  · -- Show that 25 is in the set.
    use 5
    norm_num [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
    <;> norm_num [abs_of_nonneg, abs_of_nonpos, abs]
  
  · -- Show that 25 is the minimal value in the set.
    intro x hx
    rcases hx with ⟨a, rfl⟩
    have h1 : ∑ i : Fin 10, |a - (i + 1)| ≥ 25 := by
      norm_num [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at *
      by_cases h1 : a ≥ 10
      · -- Case a ≥ 10
        rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
        linarith
  
      by_cases h9 : a ≥ 9
      · -- Case 9 ≤ a < 10
        rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
        linarith
  
      by_cases h8 : a ≥ 8
      · -- Case 8 ≤ a < 9
        rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
        linarith
  
      by_cases h7 : a ≥ 7
      · -- Case 7 ≤ a < 8
        rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
        linarith
  
      by_cases h6 : a ≥ 6
      · -- Case 6 ≤ a < 7
        rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
        linarith
  
      by_cases h5 : a ≥ 5
      · -- Case 5 ≤ a < 6
        rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
        linarith
  
      by_cases h4 : a ≥ 4
      · -- Case 4 ≤ a < 5
        rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
        linarith
  
      by_cases h3 : a ≥ 3
      · -- Case 3 ≤ a < 4
        rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
        linarith
  
      by_cases h2 : a ≥ 2
      · -- Case 2 ≤ a < 3
        rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
        linarith
  
      by_cases h1 : a ≥ 1
      · -- Case 1 ≤ a < 2
        rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
        linarith
  
      · -- Case a < 1
        rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
        linarith
  
    linarith