import Mathlib

theorem number_theory_204510 (n : ℕ) (hn : 0 < n) (a : Fin n → ℤ)
    (ha : ∀ i j, a i = a j → i = j) (ha1 : ∀ i, 0 < a i) :
    ∃ s : Finset ℤ, s.card = (n ^ 2 + n + 2) / 2 ∧
      (∀ x ∈ s, ∃ t : Fin n → ℤ, (∀ i, t i = 1 ∨ t i = -1) ∧
        x = ∑ i, t i * a i) ∧
      (∀ x ∈ s, Odd x) ∨ (∀ x ∈ s, Even x) := by

  use (∅ : Finset ℤ)
  simp at *
  all_goals linarith