import Mathlib

open Real

theorem inequalities_277195 (a₁ a₂ b₁ b₂ : ℝ) :
    a₁ * b₁ + a₂ * b₂ ≤ sqrt (a₁ ^ 2 + a₂ ^ 2) * sqrt (b₁ ^ 2 + b₂ ^ 2) ∨
    (a₁ * b₁ + a₂ * b₂) ^ 2 ≤ (a₁ ^ 2 + a₂ ^ 2) * (b₁ ^ 2 + b₂ ^ 2) := by 
  have h1 : (a₁ * b₁ + a₂ * b₂) ^ 2 ≤ (a₁ ^ 2 + a₂ ^ 2) * (b₁ ^ 2 + b₂ ^ 2) := by 
    nlinarith [sq_nonneg (a₁ * b₂ - a₂ * b₁), 
      sq_nonneg (a₁ * b₁ - a₂ * b₂), 
      sq_nonneg (a₁ - a₂), 
      sq_nonneg (b₁ - b₂),
      sq_nonneg (a₁ * b₂ - a₂ * b₁)
      ]
  right 
  linarith 
  all_goals nlinarith