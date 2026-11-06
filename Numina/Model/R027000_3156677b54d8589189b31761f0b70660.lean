import Mathlib

theorem algebra_219858 {a b c d : ℝ} (h₀ : a^2 + b^2 = 1) (h₁ : c^2 + d^2 = 1) (h₂ : a * c + b * d = 0) :
    a * b + c * d = 0 := by
  have h3 : (a^2 + b^2) * (c^2 + d^2) = 1 := by
    rw [h₀, h₁]
    norm_num
  have h4 : a * c + b * d = 0 := h₂
  have h5 : (a * d - b * c) ^ 2 = 1 := by
    nlinarith
  have h7 : a * b + c * d = 0 := by
    nlinarith [sq_nonneg (a + d), sq_nonneg (b - c), sq_nonneg (a - b), sq_nonneg (c - d), sq_nonneg (a * c - b * d), sq_nonneg (a * d + b * c), h5]
  exact h7