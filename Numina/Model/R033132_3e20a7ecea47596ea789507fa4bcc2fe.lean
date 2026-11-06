import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_148917 (x : ℝ) :
  x^2 + 2 * x + 1 - abs (x^3 + 1) - 2 * (x^2 - x + 1)^2 ≤ 0 ↔
  x ≤ 1 / 2 ∨ x ≥ 1 := by
  constructor
  · -- Forward direction: prove that if the inequality holds, then x ≤ 1/2 or x ≥ 1
    intro h
    by_cases h1 : x^3 + 1 ≥ 0
    · -- Case where x^3 + 1 ≥ 0, so abs (x^3 + 1) = x^3 + 1
      have h2 : abs (x^3 + 1) = x^3 + 1 := by
        rw [abs_of_nonneg h1]
      rw [h2] at h
      by_cases h3 : x ≤ 1 / 2
      · -- If x ≤ 1/2, then it holds
        left
        exact h3
      · -- Case where x > 1/2
        have h4 : x > 1 / 2 := by linarith
        by_cases h5 : x ≥ 1
        · -- If x ≥ 1, then it holds
          right
          linarith
        · -- Case where 1/2 < x < 1
          have h6 : x < 1 := by linarith
          nlinarith [sq_nonneg (x^2 - x), sq_nonneg (x - 1), sq_nonneg (x - 1 / 2), 
            sq_nonneg (x^2 - 1 / 4), sq_nonneg (x^2 - 1),
            sq_nonneg ((x - 1 / 2) * (x - 1)), sq_nonneg ((x - 1 / 2) * x), 
            sq_nonneg ((x) * (x - 1)), sq_nonneg ((x) * (x - 1 / 2)), 
            sq_nonneg ((x - 1) * (x - 1 / 2)), sq_nonneg ((x) * (x - 1 / 2)), 
            sq_nonneg ((x - 1) * (x - 1 / 2)), sq_nonneg (x^2 - 1 / 4)]
    · -- Case where x^3 + 1 < 0, so abs (x^3 + 1) = -(x^3 + 1)
      have h2 : abs (x^3 + 1) = - (x^3 + 1) := by
        rw [abs_of_neg (show x^3 + 1 < 0 by linarith)]
        all_goals linarith
      rw [h2] at h
      have h3 : x < -1 := by nlinarith [sq_nonneg (x + 1), sq_nonneg (x^3 + 1)]
      have h4 : x ≤ 1 / 2 := by linarith
      left
      linarith
  · -- Backward direction: prove that if x ≤ 1/2 or x ≥ 1, then the inequality holds
    rintro (h | h)
    · -- Case where x ≤ 1/2
      by_cases h1 : x^3 + 1 ≥ 0
      · -- Case where x^3 + 1 ≥ 0, abs (x^3 + 1) = x^3 + 1
        have h2 : abs (x^3 + 1) = x^3 + 1 := by
          rw [abs_of_nonneg h1]
        rw [h2]
        nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (x - 1), sq_nonneg (x^2 - 1), 
          sq_nonneg (x^2 - x), sq_nonneg (x - 1/2), sq_nonneg (x - 1), 
          sq_nonneg (x^3 - 1), sq_nonneg (x^2 - 1)]
      · -- Case where x^3 + 1 < 0, abs (x^3 + 1) = -(x^3 + 1)
        have h2 : abs (x^3 + 1) = - (x^3 + 1) := by
          rw [abs_of_neg (show x^3 + 1 < 0 by linarith)]
          all_goals linarith
          all_goals nlinarith
        rw [h2]
        nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (x - 1), sq_nonneg (x^2 - 1), 
          sq_nonneg (x^2 - x), sq_nonneg (x - 1/2), sq_nonneg (x - 1), 
          sq_nonneg (x^3 - 1), sq_nonneg (x^2 - 1)]
    · -- Case where x ≥ 1
      by_cases h1 : x^3 + 1 ≥ 0
      · -- Case where x^3 + 1 ≥ 0, abs (x^3 + 1) = x^3 + 1
        have h2 : abs (x^3 + 1) = x^3 + 1 := by
          rw [abs_of_nonneg h1]
        rw [h2]
        nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (x - 1), sq_nonneg (x^2 - 1), 
          sq_nonneg (x^2 - x), sq_nonneg (x - 1/2), sq_nonneg (x - 1), 
          sq_nonneg (x^3 - 1), sq_nonneg (x^2 - 1)]
      · -- Case where x^3 + 1 < 0, abs (x^3 + 1) = -(x^3 + 1)
        have h2 : abs (x^3 + 1) = - (x^3 + 1) := by
          rw [abs_of_neg (show x^3 + 1 < 0 by linarith)]
          all_goals linarith
          all_goals nlinarith
        rw [h2]
        nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (x - 1), sq_nonneg (x^2 - 1), 
          sq_nonneg (x^2 - x), sq_nonneg (x - 1/2), sq_nonneg (x - 1), 
          sq_nonneg (x^3 - 1), sq_nonneg (x^2 - 1)]