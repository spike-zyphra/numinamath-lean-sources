import Mathlib

theorem inequalities_155167 (a b c : ℝ) (h : a^2 + b^2 + a * b + b * c + c * a < 0) : a^2 + b^2 < c^2 := by
  nlinarith [sq_nonneg (a + b), sq_nonneg (a - b), sq_nonneg (b + c), sq_nonneg (c + a), sq_nonneg (a + b - c), sq_nonneg (b + c - a)]