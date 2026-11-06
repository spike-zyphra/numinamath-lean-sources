import Mathlib

theorem algebra_247942 (j y b : ℕ) (h₀ : j + y + b = 200)
    (h₁ : j > 2 * y) (h₂ : y > 3 * b) :
    j ≥ 121 ∧ b ≤ 19 := by 
  constructor 
  all_goals 
    omega