import Mathlib

theorem inequalities_151987 (a b c : ℝ) :
    (a^2 + b^2 + a * c)^2 + (a^2 + b^2 + b * c)^2 ≥ (a^2 + b^2) * (a + b + c)^2 := by
  nlinarith [sq_nonneg (a * (a - b) + b * (b - a)), sq_nonneg (a * c - b * c), sq_nonneg (a - b), sq_nonneg (a + b - c), sq_nonneg (a - b), sq_nonneg (c), sq_nonneg (a * c + b * c), sq_nonneg (a * b - a * c), sq_nonneg (a * b - b * c), sq_nonneg (a * b), sq_nonneg (b * c), sq_nonneg (a * c), sq_nonneg (a + b - c), sq_nonneg (a * b - a * c - b * c)]