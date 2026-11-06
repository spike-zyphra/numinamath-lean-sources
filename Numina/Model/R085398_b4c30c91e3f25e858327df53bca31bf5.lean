import Mathlib

open Real

theorem inequalities_223395 {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ)
    (y : Fin n → ℝ) (hy : ∀ i, 0 < y i) :
    ∑ i, (x i)^2 / y i ≥ (∑ i, x i)^2 / (∑ i, y i) := by
  apply Finset.sq_sum_div_le_sum_sq_div
  intro i hi
  have hyi : 0 < y i := hy i
  exact hyi