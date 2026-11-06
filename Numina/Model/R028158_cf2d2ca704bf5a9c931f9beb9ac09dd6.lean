import Mathlib

theorem inequalities_597102
    (a b c d : ℝ)
    (h₀ : a ≥ b ∧ b ≥ c ∧ c ≥ d)
    (h₁ : a + b + c + d = 9)
    (h₂ : a^2 + b^2 + c^2 + d^2 = 21) :
    a * b - c * d ≥ 2 := by
  have h₀_a : a ≥ b := h₀.1
  have h₀_b : b ≥ c := h₀.2.1
  have h₀_c : c ≥ d := h₀.2.2
  nlinarith [sq_nonneg (a - b), sq_nonneg (c - d), sq_nonneg (a + b - (c + d)), sq_nonneg (b - c)]