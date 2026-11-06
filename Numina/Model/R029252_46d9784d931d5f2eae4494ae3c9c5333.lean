import Mathlib

theorem algebra_602662 (a b c d e : ℝ) (h₀ : a + b + c + d + e = 8) (h₁ : a^2 + b^2 + c^2 + d^2 + e^2 = 16) :
    e ≤ 16 / 5 := by

  have h2 : e = 8 - (a + b + c + d) := by
    linarith

  have h3 : a^2 + b^2 + c^2 + d^2 + (8 - (a + b + c + d))^2 = 16 := by
    rw [h2] at h₁
    linarith

  have h4 : (a + b + c + d) ^2 /4 ≤ a ^ 2 + b^2 + c^2 + d^2 := by
    linarith [sq_nonneg (a + b + c + d), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d)]

  have h5 : 5 * ((a + b + c + d) ^ 2) - 64 * ((a + b + c + d)) + 192 ≤ 0 := by
    nlinarith

  nlinarith [h2, h5, sq_nonneg (e - 16 / 5), sq_nonneg (e), sq_nonneg ((a + b + c + d) - 24 / 5)]