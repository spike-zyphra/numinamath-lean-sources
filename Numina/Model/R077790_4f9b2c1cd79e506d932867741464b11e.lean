import Mathlib

theorem number_theory_303244 (d : ℕ) (h₀ : d > 0) (h₁ : d ≠ 2) (h₂ : d ≠ 5) (h₃ : d ≠ 13) :
    ∃ a b, (a = 2 ∧ b = 5) ∨ (a = 2 ∧ b = 13) ∨ (a = 5 ∧ b = 13) ∨ (a = d ∧ b = 2) ∨
    (a = d ∧ b = 5) ∨ (a = d ∧ b = 13) ∧ ¬ ∃ m, m^2 = a * b - 1 := by 
  refine' ⟨2, 5, Or.inl ⟨rfl, rfl⟩⟩