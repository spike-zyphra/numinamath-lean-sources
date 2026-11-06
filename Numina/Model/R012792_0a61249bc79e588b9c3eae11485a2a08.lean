import Mathlib

theorem algebra_135787
    (a b c A B C : ℝ)
    (h₀ : b^2 < a * c)
    (h₁ : a * C - 2 * b * B + c * A = 0) :
    B^2 ≥ A * C := by
  have h2 : a * C + c * A = 2 * b * B := by linarith
  have h3 : (a * C + c * A) ^ 2 = 4 * (b ^ 2) * (B ^ 2) := by
    have h3' : (a * C + c * A) = 2 * b * B := h2
    rw [h3']
    all_goals
      ring
  nlinarith [sq_nonneg (a * C - c * A), sq_nonneg (A * B - C * b), sq_nonneg (a * B - c * B), sq_nonneg (b * (A - C)), sq_nonneg (b ^ 2 - a * c), sq_nonneg (a * C + c * A - 2 * b * B), sq_nonneg (a * A - c * C), sq_nonneg (A * c - a * C), sq_nonneg (b * (a * C - c * A)), sq_nonneg (b * (A * b - C * b)), sq_nonneg (a * b - c * b), mul_pos (show (0 : ℝ) < a * c - b ^ 2 by nlinarith) (show (0 : ℝ) < 1 by norm_num)]