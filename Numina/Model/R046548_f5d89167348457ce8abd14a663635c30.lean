import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_18812 :
  IsLeast {y : ℝ | ∃ x, 5 * x ^ 2 + 2 * x * sqrt 5 + 1 ≥ 0 ∧ y = sqrt (5 * x ^ 2 + 2 * x * sqrt 5 + 1) + x * sqrt 5} (-1) := by
  constructor
  · -- Show -1 is in the set, using x = -1
    use -1
    have h1 : 5 * (-1 : ℝ) ^ 2 + 2 * (-1 : ℝ) * sqrt 5 + 1 ≥ 0 := by
      nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), sq_nonneg (sqrt 5 - 3)]
    constructor
    · exact h1
    · -- Show sqrt (5 * (-1 : ℝ) ^ 2 + 2 * (-1 : ℝ) * sqrt 5 + 1) + (-1 : ℝ) * sqrt 5 = -1
      have h2 : sqrt (5 * (-1 : ℝ) ^ 2 + 2 * (-1 : ℝ) * sqrt 5 + 1) = sqrt 5 - 1 := by
        have h3 : 5 * (-1 : ℝ) ^ 2 + 2 * (-1 : ℝ) * sqrt 5 + 1 = (sqrt 5 - 1) ^ 2 := by 
          nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
        rw [h3]
        have h4 : sqrt ((sqrt 5 - 1) ^ 2) = abs (sqrt 5 - 1) := by 
          rw [Real.sqrt_sq_eq_abs]
        rw [h4]
        have h5 : abs (sqrt 5 - 1) = sqrt 5 - 1 := by
          rw [abs_of_nonneg]
          nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
        rw [h5]
      rw [h2]
      nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
  · -- Show -1 is the least element in the set
    intro y hy
    rcases hy with ⟨x, h1, h2⟩
    have h4 : sqrt (5 * x ^ 2 + 2 * x * sqrt 5 + 1) + x * sqrt 5 ≥ -1 := by
      have h5 : 5 * x ^ 2 + 2 * x * sqrt 5 + 1 = (sqrt 5 * x + 1) ^ 2 := by
        nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
      have h6 : sqrt (5 * x ^ 2 + 2 * x * sqrt 5 + 1) = abs (sqrt 5 * x + 1) := by
        rw [h5]
        have h7 : sqrt ((sqrt 5 * x + 1) ^ 2) = abs (sqrt 5 * x + 1) := by 
          rw [Real.sqrt_sq_eq_abs]
        rw [h7]
      rw [h6] at *
      by_cases h7 : sqrt 5 * x + 1 ≥ 0
      · -- case 1
        rw [abs_of_nonneg h7]
        nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
      · -- case 2
        have h8 : sqrt 5 * x + 1 < 0 := by nlinarith 
        rw [abs_of_neg h8]
        nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
    linarith [h2, h4]