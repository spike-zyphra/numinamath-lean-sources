import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_52921 {S : ℕ → ℝ}
  (hS : ∀ n, ∃ a : Fin n → ℝ,
    (∀ i, 0 < a i) ∧ (∑ i, a i) = 17 ∧
    S n = ∑ k : Fin n, sqrt ((2*k+1)^2 + (a k)^2)) :
  IsLeast {n | ∃ m : ℤ, S n = m} 12 := by
  have contradictory : False := by
    specialize hS 0
    rcases hS with ⟨a, h_pos, h_sum, h_eq⟩
    simp at h_sum
    all_goals linarith
  exfalso
  exact contradictory