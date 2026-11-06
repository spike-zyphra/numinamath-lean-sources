import Mathlib

theorem algebra_322441 (a b c d : ℝ) (h₀ : a + b + c + d = 4) (h₁ : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 16 / 3) :
    a ≤ 2 := by
  have h2 : b + c + d = 4 - a := by linarith only [h₀]
  have h3 : b ^ 2 + c ^ 2 + d ^ 2 ≥ ((b + c + d) ^ 2) / 3 := by
    linarith [sq_nonneg (b - c), sq_nonneg (c - d), sq_nonneg (d - b)]
  rw [h2] at h3
  have h4 : b ^ 2 + c ^ 2 + d ^ 2 = 16 / 3 - a ^ 2 := by linarith
  have h5 : (16 / 3 - a ^ 2) ≥ ((4 - a) ^ 2) / 3 := by linarith [h3, h4]
  nlinarith [sq_nonneg (a - 2)]