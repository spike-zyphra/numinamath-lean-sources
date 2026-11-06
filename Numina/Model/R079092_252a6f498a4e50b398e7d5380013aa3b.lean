import Mathlib

theorem number_theory_148815 (a b c d e : ℕ) (h₀ : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e)
    (h₁ : b ≠ c ∧ b ≠ d ∧ b ≠ e) (h₂ : c ≠ d ∧ c ≠ e) (h₃ : d ≠ e)
    (h₄ : a + b + c + d + e = 21) (h₅ : ∃ x, a + b = x ∧ a + c = x ∧ a + d = x ∧ a + e = x)
    (h₆ : ∃ y, b + c = y ∧ b + d = y ∧ b + e = y) (h₇ : ∃ z, c + d = z ∧ c + e = z ∧ d + e = z) :
    a = 7 ∨ b = 7 ∨ c = 7 ∨ d = 7 ∨ e = 7 := by
  rcases h₅ with ⟨x, h51, h52, h53, h54⟩
  have h8 : b = c := by 
    omega
  have h9 : b ≠ c := h₁.1
  contradiction