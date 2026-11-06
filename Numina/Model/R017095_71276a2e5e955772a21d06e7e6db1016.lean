import Mathlib

theorem inequalities_141979 (t : ℝ) (ht : t > 0) : t^4 - t + 1 / 2 > 0 := by
  nlinarith [sq_nonneg (t ^ 2 - 1 / 2), sq_nonneg (t - 1), sq_nonneg (t ^ 2 - t), sq_nonneg (t ^ 2 - 1), sq_nonneg (t - (1 / 2) ^ (1 / 3 : ℝ)), sq_nonneg (t ^ 2 - 1 / 2), sq_nonneg (t - 1), sq_nonneg (t * (t - 1)), sq_nonneg ((t ^ 2) - 1 / 2), mul_pos ht ht, mul_pos ht (show 0 < t ^ 2 by positivity), mul_pos ht (show 0 < t ^ 3 by positivity)]