import Mathlib

theorem algebra_283917 {p q : ℝ} (h₀ : p^2 + 9 * q^2 + 3 * p - p * q = 30) (h₁ : p - 5 * q - 8 = 0) :
    p^2 - p - 6 = 0 := by
  have h2 : q = (p - 8) / 5 := by
    linarith
  rw [h2] at h₀
  nlinarith [sq_nonneg (p - 3 : ℝ), sq_nonneg (p + 2 : ℝ), sq_nonneg ((p - 8) / 5 + 1), sq_nonneg ((p - 8) / 5 + 2)]