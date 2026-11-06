import Mathlib

theorem inequalities_79260 (a b c d : ℝ) :
    (a + b + c + d)^2 ≤ 3 * (a^2 + b^2 + c^2 + d^2) + 6 * a * b := by 
  nlinarith [sq_nonneg (a + b - c), sq_nonneg (a + b - d), sq_nonneg (c - d), sq_nonneg (c + d - (a + b)), sq_nonneg (a - b), sq_nonneg (a + b - (c + d)), sq_nonneg (a + b + c - d), sq_nonneg (a + b - c + d)]