import Mathlib

open Real

theorem inequalities_116008 (n : ℕ) (hn : 0 < n) (e f : Fin n → ℝ)
    (hf : ∀ i, 0 < f i) :
    ∑ i, (e i)^2 / f i ≥ (∑ i, e i)^2 / ∑ i, f i := by
  have h1 : ∀ i, 0 < f i := hf
  apply Finset.sq_sum_div_le_sum_sq_div
  intro i hi
  have h2 : 0 < f i := h1 i
  positivity