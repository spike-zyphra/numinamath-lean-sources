import Mathlib

theorem inequalities_598323 (a b c d : ℝ) :
    6 * (a^2 + b^2 + c^2 + d^2) + (a + b + c + d)^2 ≥ 12 * (a * b + b * c + c * d) := by 
  nlinarith [sq_nonneg (a + b - c), sq_nonneg (b + c - d), sq_nonneg (a + d - b), sq_nonneg (a + b + c - d), sq_nonneg (a + d - c), sq_nonneg (a - b + c), sq_nonneg (a - c + d), sq_nonneg (a - d + b), sq_nonneg (a - b + c - d)]