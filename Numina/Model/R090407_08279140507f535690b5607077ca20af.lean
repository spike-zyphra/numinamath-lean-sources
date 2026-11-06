import Mathlib

theorem inequalities_127241 (a b : Fin 1987 → ℝ)
    (h₀ : ∀ i, 0 < b i) :
    (∑ i, a i) ^ 2 / ∑ i, b i ≤ ∑ i, (a i) ^ 2 / b i := by 
  apply Finset.sq_sum_div_le_sum_sq_div
  intro i hi
  exact h₀ i