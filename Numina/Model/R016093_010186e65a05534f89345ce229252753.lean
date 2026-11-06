import Mathlib

theorem inequalities_599988 (t : ℝ) (ht : t > 0) :
    t^4 - t + 1 / 2 > 0 := by
  by_cases h : t ≥ 1
  · -- Case 1: t ≥ 1
    nlinarith [sq_nonneg (t^2 - 1), sq_nonneg (t - 1), sq_nonneg (t^2 - t), sq_nonneg (t - 1)]
  · -- Case 2: t < 1
    have ht2 : t < 1 := by linarith
    nlinarith [sq_nonneg (t^2 - 1 / 2), sq_nonneg (t - 1), sq_nonneg (t^2 - t), sq_nonneg (t^2 - 1), 
      sq_nonneg (t - 1 / 2), sq_nonneg (t^2 - (t : ℝ)), 
      sq_nonneg (t ^ 2 - t + 1 / 2), 
      mul_pos ht (show 0 < 1 - t from by nlinarith)
    ]