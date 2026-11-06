import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_189918 (x : ℝ) :
  (4 * x^2 - 1) / logb 1.7 (1 / 2 * (1 - logb 7 3)) ≤ 0 ↔
  x ≤ -1 / 2 ∨ x ≥ 1 / 2 := by

  have h11 : logb (7 : ℝ) (3 : ℝ) > 0 := by
    apply logb_pos
    all_goals linarith
  have h31 : logb (7 : ℝ) (3 : ℝ) < 1 := by
    have h41 : logb (7 : ℝ) (3 : ℝ) < logb (7 : ℝ) (7 : ℝ) := by
      apply Real.logb_lt_logb
      all_goals linarith
      all_goals linarith
    have h51 : logb (7 : ℝ) (7 : ℝ) = 1 := by
      rw [logb_self_eq_one]
      all_goals linarith
    linarith [h41, h51]
  
  have h1 : logb (1.7 : ℝ) (1 / 2 * (1 - logb (7 : ℝ) (3 : ℝ)) ) < (0 : ℝ) := by
    have h10 : (1 / 2 * (1 - logb (7 : ℝ) (3 : ℝ)) : ℝ) < (1 : ℝ) := by
      nlinarith [h11, h31]
    have h5 : logb (1.7 : ℝ) (1 / 2 * (1 - logb (7 : ℝ) (3 : ℝ)) ) < logb (1.7 : ℝ) (1 : ℝ) := by
      apply Real.logb_lt_logb
      all_goals norm_num
      all_goals nlinarith
    have h4 : logb (1.7 : ℝ) (1 : ℝ) = (0 : ℝ) := by
      simp [logb_one]
    linarith [h4, h5]

  constructor
  · -- Assume (4 * x^2 - 1) / logb ... ≤ 0, prove (x ≤ -1/2 ∨ x ≥ 1/2)
    intro h
    have h71 : (4 * x^2 - 1 : ℝ) ≥ (0 : ℝ) := by
      by_contra h71
      push_neg at h71
      have h81 : (4 * x^2 - 1 : ℝ) < (0 : ℝ) := by
        linarith
      have h72 : (4 * x^2 - 1 : ℝ) / logb (1.7 : ℝ) (1 / 2 * (1 - logb (7 : ℝ) (3 : ℝ)) ) > (0 : ℝ) := by
        apply div_pos_of_neg_of_neg
        · -- Show the numerator is negative
          linarith [h81]
        · -- Show the denominator is negative
          linarith [h1]
      linarith
    by_cases h8 : x ≥ 0
    · -- If x ≥ 0, then x ≥ 1/2.
      have h9 : x ≥ (1 / 2 : ℝ) := by
        nlinarith [sq_nonneg x, h71]
      right
      linarith
    · -- x < 0
      have h9 : x ≤ (-1 / 2 : ℝ) := by
        nlinarith [sq_nonneg x, h71]
      left
      linarith
  · -- Assume x ≤ -1/2 ∨ x ≥ 1/2, prove (4 * x^2 - 1) / logb ... ≤ 0
    intro h
    rcases h with (h8 | h8)
    · -- Case x ≤ -1/2
      have h71 : (4 * x^2 - 1 : ℝ) ≥ (0 : ℝ) := by 
        nlinarith [sq_nonneg x, h8]
      have h72 : (4 * x^2 - 1 : ℝ) / logb (1.7 : ℝ) (1 / 2 * (1 - logb (7 : ℝ) (3 : ℝ)) ) ≤ (0 : ℝ) := by
        apply div_nonpos_of_nonneg_of_nonpos
        · linarith [h71]
        all_goals linarith [h1]
      linarith
    · -- Case x ≥ 1/2
      have h71 : (4 * x^2 - 1 : ℝ) ≥ (0 : ℝ) := by 
        nlinarith [sq_nonneg x, h8]
      have h72 : (4 * x^2 - 1 : ℝ) / logb (1.7 : ℝ) (1 / 2 * (1 - logb (7 : ℝ) (3 : ℝ)) ) ≤ (0 : ℝ) := by
        apply div_nonpos_of_nonneg_of_nonpos
        · linarith [h71]
        all_goals linarith [h1]
      linarith