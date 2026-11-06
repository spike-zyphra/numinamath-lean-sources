import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_8226 :
  IsLeast {n : ℝ | ∃ x, n = abs (x + 2) + abs (x + 3) + abs (x + 4)} 2 := by 
  constructor
  · -- Show 2 is in the set
    use -3
    norm_num [abs_of_nonneg, abs_of_neg]
  · -- Show 2 is a lower bound
    intro n hn
    rcases hn with ⟨x, hx⟩
    have h : abs (x + 2) + abs (x + 3) + abs (x + 4) ≥ 2 := by 
      by_cases h1 : x < -4
      · -- Case where x < -4
        rw [abs_of_neg (by linarith : x + 2 < 0), abs_of_neg (by linarith : x + 3 < 0), abs_of_neg (by linarith : x + 4 < 0)]
        linarith
      · -- Case where x ≥ -4
        by_cases h2 : x < -3
        · -- Case where -4 ≤ x < -3
          rw [abs_of_neg (by linarith : x + 2 < 0), abs_of_neg (by linarith : x + 3 < 0), abs_of_nonneg (by linarith : x + 4 ≥ 0)]
          linarith
        · -- Case where x ≥ -3
          by_cases h3 : x < -2
          · -- Case where -3 ≤ x < -2
            rw [abs_of_neg (by linarith : x + 2 < 0), abs_of_nonneg (by linarith : x + 3 ≥ 0), abs_of_nonneg (by linarith : x + 4 ≥ 0)]
            linarith
          · -- Case where x ≥ -2
            rw [abs_of_nonneg (by linarith : x + 2 ≥ 0), abs_of_nonneg (by linarith : x + 3 ≥ 0), abs_of_nonneg (by linarith : x + 4 ≥ 0)]
            linarith
    linarith [h, hx]