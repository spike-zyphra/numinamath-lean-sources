import Mathlib

theorem inequalities_276900 (a b : ℝ) (h₀ : a * b ≥ 0) :
    a^4 + 2 * a^3 * b + 2 * a * b^3 + b^4 ≥ 6 * a^2 * b^2 := by
  nlinarith [sq_nonneg (a^2 - b^2), sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a * b - a * b), sq_nonneg (a * (a - b)), sq_nonneg (b * (b - a)), sq_nonneg (a * (a + b) - b * (a + b)), sq_nonneg ((a + b) * (a - b)), sq_nonneg (a * b), sq_nonneg (a^2 - b^2)]