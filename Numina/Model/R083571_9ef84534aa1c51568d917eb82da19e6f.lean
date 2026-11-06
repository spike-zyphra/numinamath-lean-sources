import Mathlib

open Real

theorem inequalities_137672 (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ)
    (b : Fin n → ℝ) (hb : ∀ i, 0 < b i) :
    ∑ i, a i ^ 2 / b i ≥ (∑ i, a i) ^ 2 / ∑ i, b i := by
  apply Finset.sq_sum_div_le_sum_sq_div
  intro i hi
  have hbi : 0 < b i := hb i
  exact hbi