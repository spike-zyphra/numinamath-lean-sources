import Mathlib

theorem inequalities_156066 (a b : Fin 1987 → ℝ)
    (ha : ∀ i, a i ∈ Set.univ)
    (hb : ∀ i, b i > 0) :
    (∑ i, a i) ^ 2 / ∑ i, b i ≤ ∑ i, (a i) ^ 2 / b i := by 
  apply Finset.sq_sum_div_le_sum_sq_div
  intro i hi
  exact hb i