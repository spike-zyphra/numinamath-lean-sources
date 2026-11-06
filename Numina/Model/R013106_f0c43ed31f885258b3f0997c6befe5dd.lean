import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_278141 :
  IsLeast {y : ℝ | ∃ x, y = sqrt (x^2 + (x^2 / 4 - 2)^2) + sqrt (x^2 + (x^2 / 4 - 1)^2)} 3 := by
  constructor
  · -- Show 3 is in the set.
    use 0
    have h1 : sqrt (0 ^ 2 + (0 ^ 2 / 4 - 2) ^ 2) = 2 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h2 : sqrt (0 ^ 2 + (0 ^ 2 / 4 - 1) ^ 2) = 1 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h1, h2]
    all_goals norm_num
  · -- Show 3 is the least in the set
    intro y hy
    rcases hy with ⟨x, hx⟩
    have h1 : sqrt (x^2 + (x^2 / 4 - 2) ^ 2) + sqrt (x^2 + (x^2 / 4 - 1) ^ 2) ≥ 3 := by
      by_cases h : sqrt (x^2 + (x^2 / 4 - 2) ^ 2) + sqrt (x^2 + (x^2 / 4 - 1) ^ 2) - 3 < 0
      · -- We need to derive a contradiction that y < 0.
        nlinarith [sq_nonneg (sqrt (x^2 + (x^2 / 4 - 2) ^ 2) - 2), sq_nonneg (sqrt (x^2 + (x^2 / 4 - 1) ^ 2) - 1),
                  Real.sqrt_nonneg (x^2 + (x^2 / 4 - 2) ^ 2), Real.sqrt_nonneg (x^2 + (x^2 / 4 - 1) ^ 2),
                  mul_nonneg (Real.sqrt_nonneg (x^2 + (x^2 / 4 - 2) ^ 2)) (Real.sqrt_nonneg (x^2 + (x^2 / 4 - 1) ^ 2)),
                  sq_nonneg (sqrt (x^2 + (x^2 / 4 - 2) ^ 2) ^ 2 - 4), sq_nonneg (sqrt (x^2 + (x^2 / 4 - 1) ^ 2) ^ 2 - 1),
                  Real.sq_sqrt (show (0 : ℝ) ≤ x^2 + (x^2 / 4 - 2) ^ 2 by nlinarith), 
                  Real.sq_sqrt (show (0 : ℝ) ≤ x^2 + (x^2 / 4 - 1) ^ 2 by nlinarith)
                ]
      · -- Show $y \geq 3$ directly with nonlinear arithmetic solver.
        nlinarith [sq_nonneg (sqrt (x^2 + (x^2 / 4 - 2) ^ 2) - 2), sq_nonneg (sqrt (x^2 + (x^2 / 4 - 1) ^ 2) - 1),
                  Real.sqrt_nonneg (x^2 + (x^2 / 4 - 2) ^ 2), Real.sqrt_nonneg (x^2 + (x^2 / 4 - 1) ^ 2),
                  mul_nonneg (Real.sqrt_nonneg (x^2 + (x^2 / 4 - 2) ^ 2)) (Real.sqrt_nonneg (x^2 + (x^2 / 4 - 1) ^ 2)),
                  sq_nonneg (sqrt (x^2 + (x^2 / 4 - 2) ^ 2) ^ 2 - 4), sq_nonneg (sqrt (x^2 + (x^2 / 4 - 1) ^ 2) ^ 2 - 1),
                  Real.sq_sqrt (show (0 : ℝ) ≤ x^2 + (x^2 / 4 - 2) ^ 2 by nlinarith), 
                  Real.sq_sqrt (show (0 : ℝ) ≤ x^2 + (x^2 / 4 - 1) ^ 2 by nlinarith)
                ]
    linarith [ h1, hx ]