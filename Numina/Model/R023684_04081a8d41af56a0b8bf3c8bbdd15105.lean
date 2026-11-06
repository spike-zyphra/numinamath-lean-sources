import Mathlib

theorem inequalities_35677 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h₁ : a^3 = a + 1) (h₂ : b^6 = b + 3 * a) : a > b := by
  nlinarith [sq_nonneg (a^2 - 1), sq_nonneg (b^2 - 1), sq_nonneg (a - b), sq_nonneg (a^2 - b^2), sq_nonneg (a^3 - 1), sq_nonneg (b^3 - 1), sq_nonneg (a - 1), sq_nonneg (b - 1), h₁, h₂, mul_pos ha hb]