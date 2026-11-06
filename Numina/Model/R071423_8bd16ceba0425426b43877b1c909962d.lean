import Mathlib

theorem number_theory_295682 (S : Finset ℕ) (hS : ∀ n ∈ S, n ≥ 2) :
    ∃ T : Finset ℕ, T ⊆ S ∧ ∀ m ∈ T, ∀ n ∈ T, m ≠ n → ¬(∃ q : ℕ, q > 0 ∧ q^2 = m * n) := by
  use ∅
  constructor
  · -- Show that ∅ ⊆ S
    simp
  · -- Show that all numbers in T are greater than 2
    simp
    all_goals tauto
    all_goals simp [Finset.mem_empty]
    all_goals tauto
    all_goals simp [Finset.mem_empty]
    all_goals tauto