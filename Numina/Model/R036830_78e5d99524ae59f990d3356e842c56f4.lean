import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_309680 {S : ℕ → ℝ}
  (hS : ∀ n, ∃ a : Fin n → ℝ,
    (∀ i, 0 < a i) ∧ (∑ i, a i) = 17 ∧
    S n = ∑ k, sqrt ((2*k - 1)^2 + (a k)^2)) :
  IsLeast {n | ∃ m : ℤ, S n = m} 12 := by

  have h0 : ∃ a : Fin 0 → ℝ, (∀ i, 0 < a i) ∧ (∑ i : Fin 0, a i) = 17 ∧ S 0 = ∑ k : Fin 0, sqrt ((2*k - 1)^2 + (a k)^2) := hS 0
  rcases h0 with ⟨a, ha_pos, ha_sum, hS₁⟩
  simp at ha_sum hS₁
  all_goals linarith