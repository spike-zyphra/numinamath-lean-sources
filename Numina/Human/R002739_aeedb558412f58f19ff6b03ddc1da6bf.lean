import Mathlib

theorem number_theory_106436 (s : Finset ℕ) (h₀ : s.card = 4) (h₁ : ∀ x ∈ s, x > 0)
    (h₂ : ∀ w ∈ Finset.Icc 1 1985, ∃ s' : Finset ℕ, s' ⊆ s ∧ ∑ x ∈ s', x = w) :
    s.card = 4 := by 
  exact h₀