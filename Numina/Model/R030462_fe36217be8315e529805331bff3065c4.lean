import Mathlib

theorem number_theory_275296 (grandma granddaughter : ℕ) (h₀ : grandma < 100) (h₁ : granddaughter > 10)
    (h₂ : grandma % granddaughter = 0) (h₃ : 1000 * granddaughter + grandma - (1000 * grandma + granddaughter) = 7128) :
    (grandma, granddaughter) = (12, 84) ∨ (grandma, granddaughter) = (18, 90) ∨ (grandma, granddaughter) = (24, 96) := by
  omega