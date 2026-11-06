import Mathlib

theorem algebra_279131 (girls boys : ℕ) (h₀ : girls + boys = 50) (h₁ : 6 ∣ girls) (h₂ : 8 ∣ boys)
    (h₃ : girls / 6 + boys / 8 = girls + boys - 43) :
    girls = 18 := by
  rcases h₁ with ⟨k, hk⟩
  rcases h₂ with ⟨m, hm⟩
  have h4 : 6 * k + 8 * m = 50 := by
    omega
  have h5 : k + m = 7 := by
    omega
  omega