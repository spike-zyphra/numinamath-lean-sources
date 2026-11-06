import Mathlib

theorem number_theory_206595 (n : ℕ) (hn : 4 ≤ n) (s : Finset ℕ)
    (h₀ : s ⊆ Finset.Icc 1 (2 * n - 1)) (h₁ : s.card = n) :
    ∃ t ⊆ s, (2 * n) ∣ ∑ i ∈ t, i := by 
  use ∅
  constructor
  · -- Show ∅ ⊆ s
    simp
  · -- Show (2 * n) ∣ ∑ i ∈ (∅ : Finset ℕ), i 
    simp
    all_goals try { tauto }