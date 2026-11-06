import Mathlib

theorem inequalities_103448 (a b : ℝ) (h₀ : 0 < b) (h₁ : b < a) :
    4 * a^3 * (a - b) ≥ a^4 - b^4 := by
  have h2 : 0 < a := by linarith
  suffices 3 * a^4 - 4 * a^3 * b + b^4 ≥ 0 by
    nlinarith
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a - 2 * b), sq_nonneg (2 * a - b),
    sq_nonneg (a^2 - b^2), sq_nonneg (a^2 - a * b), sq_nonneg (a * b - b^2),
    mul_pos (show 0 < a - b by linarith) (show 0 < a by linarith), mul_pos (show 0 < a - b by linarith) (show 0 < b by linarith), sq_nonneg (3 * a^2 + 2 * a * b + b^2)]