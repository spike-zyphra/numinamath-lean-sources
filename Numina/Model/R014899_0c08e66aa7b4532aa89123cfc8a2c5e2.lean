import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_225707 (x : Fin 5 → ℝ)
  (h₀ : ∀ i, 0 ≤ x i)
  (h₁ : ∑ i, x i = 1) :
  x 0 * x 1 + x 1 * x 2 + x 2 * x 3 + x 3 * x 4 ≤ 1 / 4 := by
  have h20 : x 0 + x 1 + x 2 + x 3 + x 4 = 1 := by
    simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at h₁ ⊢
    linarith
  have h21 : 0 ≤ x 0 := by apply h₀ 
  have h22 : 0 ≤ x 1 := by apply h₀ 
  have h23 : 0 ≤ x 2 := by apply h₀
  have h24 : 0 ≤ x 3 := by apply h₀ 
  have h25 : 0 ≤ x 4 := by apply h₀ 
  nlinarith [sq_nonneg (x 0 + x 2 + x 4 - (x 1 + x 3)), 
            sq_nonneg (x 1 - x 2), 
            sq_nonneg (x 3 - x 0), 
            sq_nonneg (x 1 + x 3 - 1 / 2), 
            sq_nonneg (x 2 - 1 / 2), 
            h₀ 0, h₀ 1, h₀ 2, h₀ 3, h₀ 4, 
            mul_nonneg (show 0 ≤ x 0 by apply h₀) (show 0 ≤ x 1 by apply h₀), 
            mul_nonneg (show 0 ≤ x 1 by apply h₀) (show 0 ≤ x 2 by apply h₀), 
            mul_nonneg (show 0 ≤ x 2 by apply h₀) (show 0 ≤ x 3 by apply h₀), 
            mul_nonneg (show 0 ≤ x 3 by apply h₀) (show 0 ≤ x 4 by apply h₀)]