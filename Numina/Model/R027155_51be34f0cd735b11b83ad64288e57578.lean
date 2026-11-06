import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_133679 {S : ℕ → ℝ}
  (hS : ∀ n, ∃ a : Fin n → ℝ,
    (∀ k, 0 < a k) ∧ (∑ k, a k) = 17 ∧
    S n = ∑ k, sqrt ((2*k - 1)^2 + (a k)^2)) :
  IsLeast {n | ∃ m : ℤ, S n = m} 12 := by
  have h1 := hS 0
  rcases h1 with ⟨a, ha_pos, ha_sum, hS0⟩
  simp [Finset.sum_empty] at ha_sum
  all_goals linarith