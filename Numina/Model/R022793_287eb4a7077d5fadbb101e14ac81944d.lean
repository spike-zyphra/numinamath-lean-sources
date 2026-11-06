import Mathlib

theorem algebra_165409 (a b c : ℕ) (h₀ : a + b + c = 168) (h₁ : b = 3 * a) (h₂ : c = 4 * a) :
    a = 21 ∧ b = 63 ∧ c = 84 := by 
  have h3 : a = 21 := by
    omega
  have h4 : b = 63 := by 
    omega
  have h5 : c = 84 := by
    omega
  exact ⟨h3, h4, h5⟩