import Mathlib

open Real

theorem algebra_300757 : sqrt (7 - 4 * sqrt 3) < sqrt (5 - 2 * sqrt 6) := by
  have h1 : 0 ≤ (7 - 4 * sqrt 3 : ℝ) := by
    nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  have h2 : 0 ≤ (5 - 2 * sqrt 6 : ℝ) := by
    nlinarith [Real.sqrt_nonneg (6 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]
  have h3 : (7 - 4 * sqrt 3 : ℝ) < (5 - 2 * sqrt 6 : ℝ) := by
    nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sqrt_nonneg (6 : ℝ), 
              Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), 
              Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), 
              mul_nonneg (Real.sqrt_nonneg (3)) (Real.sqrt_nonneg (6)), 
              sq_nonneg (Real.sqrt (3) - 1), sq_nonneg (Real.sqrt (6) - 2), sq_nonneg (Real.sqrt (3) - Real.sqrt (6) / 2), 
              Real.sqrt_le_sqrt (by norm_num : (3 : ℝ) ≤ (6 : ℝ)), 
              Real.sqrt_nonneg (3), Real.sqrt_nonneg (6)]
  have h4 : sqrt (7 - 4 * sqrt 3) < sqrt (5 - 2 * sqrt 6) := by
    apply Real.sqrt_lt_sqrt
    linarith [h1]
    linarith [h3, h2]
  exact h4