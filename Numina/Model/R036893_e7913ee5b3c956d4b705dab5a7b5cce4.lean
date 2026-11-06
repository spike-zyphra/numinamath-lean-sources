import Mathlib

theorem inequalities_212081
    (a b c d : ℝ)
    (h₀ : a ≥ b ∧ b ≥ c ∧ c ≥ d)
    (h₁ : a + b + c + d = 9)
    (h₂ : a^2 + b^2 + c^2 + d^2 = 21) :
    a * b - c * d ≥ 2 := by
  rcases h₀ with ⟨h₃, h₄, h₅⟩
  nlinarith [sq_nonneg (a - b), sq_nonneg (c - d), sq_nonneg (a + b - c - d), sq_nonneg (b - c)]