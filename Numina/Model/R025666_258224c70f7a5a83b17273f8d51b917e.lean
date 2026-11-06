import Mathlib

theorem inequalities_57842 (a : ℝ) : 3*(a^4+a^2+1) ≥ (a^2+a+1)^2 := by
  nlinarith [sq_nonneg (a - 1), sq_nonneg (a^2 + a + 1), sq_nonneg (a * (a - 1)), sq_nonneg ((a^2 - a + 1)), sq_nonneg (a - 1), sq_nonneg ( (a * 1) - a), sq_nonneg ((a * 1) + (a * (a - 1))), sq_nonneg ((a + 1) - (a)), sq_nonneg ((a ^ 2 - a + 1) - (a) ) ]