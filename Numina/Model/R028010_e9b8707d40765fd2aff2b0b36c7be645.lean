import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_120210 :
  IsGreatest {y : ℝ | ∃ x, y = sqrt (2 * x ^ 2 + 2 * x + 41) - sqrt (2 * x ^ 2 + 4 * x + 4)} 5 := by
  constructor
  · -- Show 5 is in the range
    use -8 / 7
    have h3 : sqrt (2 * (-8 / 7) ^ 2 + 2 * (-8 / 7) + 41) = (45 / 7 : ℝ) := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h4 : sqrt (2 * (-8 / 7) ^ 2 + 4 * (-8 / 7) + 4) = (10 / 7 : ℝ) := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h3, h4]
    norm_num
  · -- Show 5 is the greatest
    intro y hy
    rcases hy with ⟨x, hx⟩
    have h1 : sqrt (2 * x ^ 2 + 2 * x + 41) - sqrt (2 * x ^ 2 + 4 * x + 4) ≤ 5 := by
      have h2 : sqrt (2 * x ^ 2 + 2 * x + 41) ≤ 5 + sqrt (2 * x ^ 2 + 4 * x + 4) := by
        have h3 : (5 + sqrt (2 * x ^ 2 + 4 * x + 4)) ^ 2 ≥ (2 * x ^ 2 + 2 * x + 41 : ℝ) := by
          have h10 : (5 + sqrt (2 * x ^ 2 + 4 * x + 4)) ^ 2 = 25 + 10 * sqrt (2 * x ^ 2 + 4 * x + 4) + (sqrt (2 * x ^ 2 + 4 * x + 4) ^ 2 : ℝ) := by
            ring
          rw [h10]
          have h11 : sqrt (2 * x ^ 2 + 4 * x + 4) ^ 2 = (2 * x ^ 2 + 4 * x + 4 : ℝ) := by
            apply Real.sq_sqrt
            nlinarith [sq_nonneg (x + 1 : ℝ)]
          rw [h11]
          nlinarith [Real.sqrt_nonneg (2 * x ^ 2 + 4 * x + 4), sq_nonneg (7 * x + 8 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 * x ^ 2 + 4 * x + 4 : ℝ) by nlinarith [sq_nonneg (x + 1 : ℝ)])]
        have h3' : (5 + sqrt (2 * x ^ 2 + 4 * x + 4)) ≥ 0 := by
          nlinarith [Real.sqrt_nonneg (2 * x ^ 2 + 4 * x + 4), Real.sq_sqrt (show (0 : ℝ) ≤ (2 * x ^ 2 + 4 * x + 4 : ℝ) by nlinarith [sq_nonneg (x + 1 : ℝ)]) ]
        have h4 : sqrt (2 * x ^ 2 + 2 * x + 41) ≥ 0 := by
          positivity
        nlinarith [Real.sqrt_nonneg (2 * x ^ 2 + 2 * x + 41), Real.sq_sqrt (show (0 : ℝ) ≤ (2 * x ^ 2 + 2 * x + 41 : ℝ) by nlinarith [sq_nonneg (x : ℝ), sq_nonneg (x + 1 : ℝ)]), Real.sq_sqrt (show (0 : ℝ) ≤ (2 * x ^ 2 + 4 * x + 4 : ℝ) by nlinarith [sq_nonneg (x + 1 : ℝ)]) ]
      linarith
    linarith [h1, hx]