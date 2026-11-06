import Mathlib

theorem number_theory_194104 (s : Finset ℕ) (h₀ : s.card = 50)
    (h₁ : ∀ n ∈ s, n > 0) (h₂ : ∀ n ∈ s, n ≤ 100) :
    ∃ t ⊆ s, ∃ m, t.sum id = m^2 := by 
  use ∅ 
  constructor 
  · 
    simp 
  · 
    use 0
    all_goals 
      simp