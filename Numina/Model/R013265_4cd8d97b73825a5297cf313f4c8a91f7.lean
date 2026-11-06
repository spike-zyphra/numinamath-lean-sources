import Mathlib

theorem algebra_602650 (a b c d : ℝ)
    (h₀ : a^2 + b^2 = 1) (h₁ : c^2 + d^2 = 1) (h₂ : a * c + b * d = 0) :
    a * b + c * d = 0 := by
  have h3 : a ^ 2 + b ^ 2 = 1 := h₀
  have h4 : c ^ 2 + d ^ 2 = 1 := h₁
  have h5 : a * c + b * d = 0 := h₂
  nlinarith [sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (a + d), sq_nonneg (b + c), sq_nonneg (a * d - b * c), sq_nonneg (a * b - c * d), sq_nonneg (a * c - b * d), sq_nonneg (a * d + b * c)]