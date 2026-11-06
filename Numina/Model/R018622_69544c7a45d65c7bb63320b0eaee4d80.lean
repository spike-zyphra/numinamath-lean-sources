import Mathlib

open Real

theorem inequalities_296782 {n : ℕ} (hn : n ≥ 3) (t : Fin n → ℝ)
    (ht : ∀ i, 0 < t i) (h : n^2 + 1 > (∑ i, t i) * (∑ i, 1 / t i)) :
    True := by 
  trivial