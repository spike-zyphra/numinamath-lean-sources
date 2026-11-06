import Mathlib

theorem algebra_145130 (c j t : ℕ) (h₀ : (c - 5) * 10 = (j - 5) * 9 ∧ (j - 5) * 13 = (t - 5) * 10)
    (h₁ : (c + 10) * 15 = (j + 10) * 14 ∧ (j + 10) * 18 = (t + 10) * 13) :
    c = 32 ∧ j = 35 ∧ t = 44 := by
  rcases h₀ with ⟨h₀₁, h₀₂⟩
  rcases h₁ with ⟨h₁₁, h₁₂⟩
  have h1 : c = 32 := by
    omega
  have h2 : j = 35 := by
    omega
  have h3 : t = 44 := by
    omega
  exact ⟨h1, h2, h3⟩