import Mathlib

theorem algebra_202777 (S : Finset ℚ) (hS : S.card = 100)
    (hS1 : ∀ x ∈ S, ∃ n : ℕ, x = 1 / (n + 1)) :
    S.card = 1 → ∃ x ∈ S, x = 100 := by
  intro hFinal
  rw [hS] at hFinal
  norm_num at hFinal