import Mathlib

theorem algebra_57062 (a b c : ℝ) (h₀ : ∃ x, x^3 - a * x^2 + b = 0 ∧ x^3 - b * x^2 + c = 0)
    (h₁ : ∃ x, x^3 - b * x^2 + c = 0 ∧ x^3 - c * x^2 + a = 0) (h₂ : ∃ x, x^3 - c * x^2 + a = 0 ∧ x^3 - a * x^2 + b = 0) :
    a = b ∧ b = c := by
  rcases h₀ with ⟨x₀, h₀₁, h₀₂⟩
  rcases h₁ with ⟨x₁, h₁₁, h₁₂⟩ 
  rcases h₂ with ⟨x₂, h₂₁, h₂₂⟩
  have eq1 : a = b := by
    nlinarith [sq_nonneg (x₀ - x₁), sq_nonneg (x₀ - x₂), sq_nonneg (x₁ - x₂), 
      sq_nonneg (x₀^2 - 1), sq_nonneg (x₁^2 - 1), sq_nonneg (x₂^2 - 1), 
      sq_nonneg (x₀ * x₁), sq_nonneg (x₀ * x₂), sq_nonneg (x₁ * x₂)
    ]
  have eq2 : b = c := by
    nlinarith [sq_nonneg (x₀ - x₁), sq_nonneg (x₀ - x₂), sq_nonneg (x₁ - x₂), 
      sq_nonneg (x₀^2 - 1), sq_nonneg (x₁^2 - 1), sq_nonneg (x₂^2 - 1), 
      sq_nonneg (x₀ * x₁), sq_nonneg (x₀ * x₂), sq_nonneg (x₁ * x₂)
    ]
  constructor 
  · linarith [eq1] 
  · linarith [eq2]