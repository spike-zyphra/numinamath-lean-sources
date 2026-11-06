import Mathlib

theorem inequalities_307360 (a b c d : ℝ)
    (h₀ : a + b + c + d = 3) (h₁ : a * b + a * c + a * d + b * c + b * d + c * d = 3) :
    a + b + c + 2 * a * b + 2 * b * c + 2 * c * a ≥ 2 * d := by
  have h2 : a + b + c = 3 - d := by linarith
  have h3 : a * b + b * c + c * a = 3 - 3 * d + d ^ 2 := by
    have eq1 : a * b + a * c + a * d + b * c + b * d + c * d = 3 := h₁
    have eq2 : a * b + b * c + c * a + d * (a + b + c) = 3 := by
      nlinarith [eq1]
    have eq3 : a + b + c = 3 - d := by linarith [h₀]
    rw [eq3] at eq2
    nlinarith [eq2]
  nlinarith [sq_nonneg (a + b + c - d), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), sq_nonneg (d - 3/2), h2, h3]