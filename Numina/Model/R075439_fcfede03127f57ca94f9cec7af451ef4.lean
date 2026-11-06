import Mathlib

theorem algebra_293301 (S : Finset ℕ) (hS : S.card = 2020)
    (hS1 : ∀ x ∈ S, x ∈ Finset.Icc 1 2020) :
    ∃ T : Finset ℕ, T ⊆ S ∧ (∀ x ∈ T, ∃ y ∈ T, x ≠ y ∧ x^2 - y * x + y = 0) := by 
  use ∅
  simp