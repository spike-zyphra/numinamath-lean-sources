import Mathlib

open Real Set
open scoped BigOperators

theorem number_theory_251349 :
  IsGreatest {x | ∃ n : ℕ, 1 ≤ n ∧ n ≤ 2020 ∧ x = (n : ℝ) ^ (1 / n)} (3 ^ (1 / 3)) := by
  constructor
  · -- Show that (3 : ℝ) ^ (1 / 3) is in the set.
    use 3
    all_goals norm_num
  · -- Show that (3 : ℝ) ^ (1 / 3) is the greatest element in the set.
    intro x hx
    rcases hx with ⟨n, hn1, hn2, hx⟩
    by_contra h
    push_neg at h
    have h3 : (n : ℝ) ^ (1 / n) > (3 : ℝ) ^ (1 / 3) := by linarith [h, hx]
    by_cases h4 : n ≤ 2020
    · -- Since n is bounded, we can check each value
      interval_cases n <;> norm_num at h3 hx ⊢
      all_goals
        norm_num at h3 ⊢
        all_goals
          nlinarith [Real.rpow_pos_of_pos (show (0 : ℝ) < (2 : ℝ) by norm_num) (1 / 2), 
            Real.rpow_pos_of_pos (show (0 : ℝ) < (3 : ℝ) by norm_num) (1 / 3), 
            sq_nonneg ((2 : ℝ) ^ (1 / 2 : ℝ) - (3 : ℝ) ^ (1 / 3 : ℝ)), 
            sq_nonneg ((3 : ℝ) ^ (1 / 3 : ℝ) - (1.442 : ℝ)), 
            sq_nonneg ((2 : ℝ) ^ (1 / 2 : ℝ) - (1.414 : ℝ)), 
            Real.rpow_pos_of_pos (show (0 : ℝ) < (2 : ℝ) by norm_num) (1 / 2), 
            Real.rpow_pos_of_pos (show (0 : ℝ) < (3 : ℝ) by norm_num) (1 / 3)
          ]
    · -- n > 2020
      linarith