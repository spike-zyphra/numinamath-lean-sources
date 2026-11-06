import Mathlib

theorem algebra_2527 {x : ℝ} : (x^2 + x - 1 : ℝ) = (x + (1 - Real.sqrt 5) / 2) * (x + (1 + Real.sqrt 5) / 2) := by
  nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), sq_nonneg (Real.sqrt 5), sq_nonneg (x)]