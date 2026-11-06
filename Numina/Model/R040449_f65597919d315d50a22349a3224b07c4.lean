import Mathlib

open Real
open scoped BigOperators

theorem inequalities_600534 {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ)
  (hx : ∀ i, 0 < x i) (q : Fin n → ℝ) (hq : ∀ i, 0 < q i)
  (hsum : ∑ i, q i = 1) :
  ∏ i, (x i) ^ (q i) ≤ ∑ i, q i * x i := by 
  have h1 : (∀ i, 0 ≤ x i) := fun i => le_of_lt (hx i)
  have h2 : (∀ i, 0 ≤ q i) := fun i => le_of_lt (hq i)
  have h3 : (∑ i, q i) = 1 := hsum
  have h4 : ∏ i, (x i) ^ (q i) ≤ ∑ i, q i * x i := by 
    apply Real.geom_mean_le_arith_mean_weighted
    all_goals 
      try { simp_all }
  linarith