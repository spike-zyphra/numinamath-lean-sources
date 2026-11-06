import Mathlib

open Real

theorem inequalities_188064 {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ)
    (y : Fin n → ℤ) (hy : ∀ i, 0 < y i) :
    ∑ i, (x i)^2 / (y i : ℝ) ≥ (∑ i, x i)^2 / (∑ i, y i : ℝ) := by 
  have h1 : ∀ i, (0 : ℝ) < y i := by 
    intro i
    have h2 := hy i
    exact_mod_cast (show (0 : ℤ) < y i by linarith)
  have h2 : ∑ i, (x i) ^ 2 / (y i : ℝ) ≥ (∑ i, (x i)) ^ 2 / (∑ i, (y i : ℝ)) := by
    apply Finset.sq_sum_div_le_sum_sq_div
    intro i hi
    specialize h1 i
    simpa using h1
  exact_mod_cast h2