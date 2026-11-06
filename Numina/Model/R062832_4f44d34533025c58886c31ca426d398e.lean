import Mathlib

theorem algebra_603023 (a b c d e : ℝ)
    (h₁ : a + b + c + d + e = 8) (h₂ : a^2 + b^2 + c^2 + d^2 + e^2 = 16) :
    0 ≤ e ∧ e ≤ 16 / 5 := by
  have h₃ : a + b + c + d = 8 - e := by linarith
  have h₄ : a^2 + b^2 + c^2 + d^2 = 16 - e^2 := by linarith
  have h₅ : 4 * (a^2 + b^2 + c^2 + d^2) - (a + b + c + d)^2 ≥ 0 := by
    linarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d)]
  rw [h₃, h₄] at h₅
  constructor
  · nlinarith
  · nlinarith