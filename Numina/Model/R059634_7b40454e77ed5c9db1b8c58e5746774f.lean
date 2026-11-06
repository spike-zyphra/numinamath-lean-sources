import Mathlib

theorem inequalities_292319 (a b : ℝ) : a^2 + b^2 + 7/4 ≥ a*b + 2*a + b/2 := by
  nlinarith [sq_nonneg (a - (b + 2) / 2), sq_nonneg (b - 1)]