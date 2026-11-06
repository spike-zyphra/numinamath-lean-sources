import Mathlib

theorem inequalities_601196 (t : ℝ) : t ^ 4 - t + 1 / 2 > 0 := by
  nlinarith [sq_nonneg (t ^ 2 - 1 / 2), sq_nonneg (t ^ 2 - t), sq_nonneg (t - 1), sq_nonneg (t + 1), sq_nonneg (t ^ 2 - 1 / 2), sq_nonneg (t ^ 2 + 1 / 2)]