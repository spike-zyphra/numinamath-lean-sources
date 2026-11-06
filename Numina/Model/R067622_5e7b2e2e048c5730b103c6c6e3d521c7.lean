import Mathlib

open Real
open scoped BigOperators

theorem algebra_175036 {ξ : Fin 6 → ℝ} (hξ : ∀ i, ξ i = i + 1)
  (η : Fin 6 → ℝ) (hη : ∀ i, η i = min (ξ i) 3) :
  (∑ i, η i * (1 / 6)) = 5 / 2 ∧ (∑ i, (η i - 5 / 2) ^ 2 * (1 / 6)) = 7 / 12 := by
  constructor
  · -- Show expectation is 5/2
    simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, hξ, hη]
    all_goals norm_num
  · -- Show variance is 7/12
    simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, hξ, hη]
    all_goals norm_num