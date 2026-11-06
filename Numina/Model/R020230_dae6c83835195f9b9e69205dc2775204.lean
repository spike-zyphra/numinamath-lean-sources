import Mathlib

theorem number_theory_238779 (a b c : ℤ) (h₀ : a > 0) (h₁ : b > 0) (h₂ : c > 0)
    (h₃ : a^2 + b^2 = c^2) (h₄ : (1/2) * a * b = 2 * (a + b + c)) :
    (a = 3 ∧ b = 4 ∧ c = 5) ∨ (a = 5 ∧ b = 12 ∧ c = 13) ∨ (a = 12 ∧ b = 16 ∧ c = 17) := by 
  omega