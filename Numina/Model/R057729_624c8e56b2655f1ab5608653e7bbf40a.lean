import Mathlib

open Real

theorem inequalities_602671 (a : Fin 1987 → ℝ) (b : Fin 1987 → ℝ)
    (h₀ : ∀ i, b i > 0) :
    (∑ i, a i) ^ 2 / ∑ i, b i ≤ ∑ i, (a i) ^ 2 / b i := by
  apply Finset.sq_sum_div_le_sum_sq_div
  intro i hi
  exact h₀ i