import Mathlib

theorem algebra_125482 (a b c d : ℝ)
    (h₀ : a^2 + b^2 = 1) (h₁ : c^2 + d^2 = 1) (h₂ : a * c + b * d = 0) :
    a * b + c * d = 0 := by
  have h4 : a^2 = d^2 := by
    nlinarith [sq_nonneg (a - d), sq_nonneg (b + c), sq_nonneg (a + d), sq_nonneg (b - c)]
  have h5 : b^2 = c^2 := by
    nlinarith [sq_nonneg (a - d), sq_nonneg (b + c), sq_nonneg (a + d), sq_nonneg (b - c)]
  have h3 : (a * b + c * d) ^ 2 = (a^2 - d^2) * (b^2 - c^2) := by
    nlinarith [sq_nonneg (a - d), sq_nonneg (b + c), sq_nonneg (a + d), sq_nonneg (b - c)]
  rw [show a^2 - d^2 = (0 : ℝ) by nlinarith [h4], show b^2 - c^2 = (0 : ℝ) by nlinarith [h5]] at h3
  have h6 : (a * b + c * d) ^ 2 = 0 := by
    nlinarith
  have h7 : a * b + c * d = 0 := by
    nlinarith
  exact h7