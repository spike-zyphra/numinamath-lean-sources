import Mathlib

theorem inequalities_200534 (a b : Fin 1987 → ℝ) (hb : ∀ i, 0 < b i) :
    (∑ i, a i) ^ 2 / ∑ i, b i ≤ ∑ i, a i ^ 2 / b i := by
  have h1 : ∀ i, 0 < b i := hb
  have h3 : ∀ i, 0 < b i := h1
  have h6 : (∑ i : Fin 1987, a i) ^ 2 / (∑ i : Fin 1987, b i) ≤ ∑ i : Fin 1987, (a i ^ 2 / b i) := by
    apply Finset.sq_sum_div_le_sum_sq_div
    all_goals
      intro i hi
      specialize h1 i
      simpa using h1
  simpa using h6