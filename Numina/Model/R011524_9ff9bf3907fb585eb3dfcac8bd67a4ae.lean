import Mathlib

theorem inequalities_4918 (a b : ℝ) : 8 * (a ^ 4 + b ^ 4) ≥ (a + b) ^ 4 := by 
  nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a * b), sq_nonneg (a - b), sq_nonneg (a + b), 
      sq_nonneg (a^2 + b^2 - 2 * a * b), sq_nonneg (a^2 + b^2 + 2 * a * b), 
      sq_nonneg (a^2 - b^2), sq_nonneg (a^3 - a^2 * b), sq_nonneg (a * b^2 - b^3),
      sq_nonneg (a^3 - b^3)]