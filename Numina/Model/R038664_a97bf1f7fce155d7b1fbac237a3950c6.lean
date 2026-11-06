import Mathlib

theorem inequalities_85928 (a b c d : ℝ) : (a ^ 2 + b ^ 2 + 1) * (c ^ 2 + d ^ 2 + 1) ≥ 2 * (a + c) * (b + d) := by 
  nlinarith [sq_nonneg (a * c - b * d), sq_nonneg (a * d + b * c - 1), sq_nonneg (a - b), sq_nonneg (c - d), sq_nonneg (a * c + b * d - (a * d + b * c)), sq_nonneg (a + b - c - d), sq_nonneg (a - b + c - d), sq_nonneg (a * d - b * c), sq_nonneg (a * c + d * b - 1), sq_nonneg (a * d + b * c - (a * c + b * d)), sq_nonneg (a * d - b * c), sq_nonneg (a + d - (b + c)), sq_nonneg (a * b - c * d)]