import Mathlib

theorem algebra_301801 {a b c d : ℝ} (h₀ : a^2 + b^2 = 1) (h₁ : c^2 + d^2 = 1)
    (h₂ : a * c + b * d = 0) :
    a^2 + c^2 = 1 ∧ b^2 + d^2 = 1 ∧ a * b + c * d = 0 := by
  have h3 : a^2 + c^2 = 1 := by
    nlinarith [sq_nonneg (a - c), sq_nonneg (b - d), sq_nonneg (a + c), sq_nonneg (b + d), sq_nonneg (a * d - b * c)]
  -- Prove b^2 + d^2 = 1
  have h4 : b^2 + d^2 = 1 := by
    nlinarith [sq_nonneg (a - c), sq_nonneg (b - d), sq_nonneg (a + c), sq_nonneg (b + d), sq_nonneg (a * d - b * c)]
  -- Prove a * b + c * d = 0
  have h5 : a * b + c * d = 0 := by
    nlinarith [sq_nonneg (a * d - b * c), sq_nonneg (a * b - c * d), h₀, h₁, h₂, h3, h4]
  exact ⟨h3, h4, h5⟩