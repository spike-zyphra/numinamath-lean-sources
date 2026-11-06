import Mathlib

theorem inequalities_49841 (a b c d : ℝ) (h₀ : a ≥ b ∧ b ≥ c ∧ c ≥ d)
    (h₁ : a + b + c + d = 13) (h₂ : a^2 + b^2 + c^2 + d^2 = 43) :
    a * b ≥ 3 + c * d := by
  have h3 : a ≥ b := h₀.1
  have h4 : b ≥ c := h₀.2.1
  have h5 : c ≥ d := h₀.2.2
  nlinarith [sq_nonneg (a - b), sq_nonneg (c - d), sq_nonneg (a + b - (c + d)), sq_nonneg (b - c)]