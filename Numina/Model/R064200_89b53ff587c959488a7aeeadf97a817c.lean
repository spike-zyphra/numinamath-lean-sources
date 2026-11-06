import Mathlib

open Real
open scoped BigOperators

theorem inequalities_221109 {n : ℕ} (hn : 0 < n) (a b : Fin n → ℝ)
  (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) :
  ∑ i, (b i)^2 / a i ≥ (∑ i, b i)^2 / ∑ i, a i := by
  apply Finset.sq_sum_div_le_sum_sq_div
  all_goals
    intro i hi
    have ha_i : a i > 0 := ha i
    exact ha_i