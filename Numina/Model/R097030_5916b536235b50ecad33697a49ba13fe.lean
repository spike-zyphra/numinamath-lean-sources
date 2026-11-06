import Mathlib

theorem algebra_280637 {g b : ℕ} (h₀ : g + b = 24) (h₁ : g * 5 = b * 3) :
    g < b ∧ b - g = 6 := by
  have h2 : b = 15 := by
    omega
  have h3 : g = 9 := by
    omega
  have h4 : g < b := by
    omega
  have h5 : b - g = 6 := by
    omega
  exact ⟨h4, h5⟩