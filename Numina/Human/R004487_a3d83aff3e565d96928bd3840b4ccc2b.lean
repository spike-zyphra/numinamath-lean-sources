import Mathlib

theorem algebra_274290 {a b c : ℝ} (h₀ : a * 3 = b * 2) (h₁ : b * 4 = c * 3) (h₂ : a * b + b * c + c * a = 13) :
    b * c = 6 := by 
  have h₃ : a = 2 / 3 * b := by linarith
  have h₄ : c = 4 / 3 * b := by linarith
  nlinarith [sq_nonneg (a - 2 / 3 * b), sq_nonneg (c - 4 / 3 * b), sq_nonneg (b - 3 / 2), sq_nonneg (a - 1), sq_nonneg (c - 2),
    sq_nonneg (a - 2), sq_nonneg (c - 4)]