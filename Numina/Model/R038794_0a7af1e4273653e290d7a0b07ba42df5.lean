import Mathlib

open Real

theorem algebra_312758 : 4 * sqrt (3 + 2 * sqrt 2) - sqrt (41 + 24 * sqrt 2) = 1 := by
  have h1 : sqrt (3 + 2 * sqrt 2) = 1 + Real.sqrt 2 := by
    have h2 : (3 + 2 * sqrt 2 : ℝ) = (1 + Real.sqrt 2) ^ 2 := by
      nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    rw [h2]
    have h3 : sqrt ((1 + Real.sqrt 2) ^ 2) = 1 + Real.sqrt 2 := by
      rw [Real.sqrt_sq (show 0 ≤ (1 + Real.sqrt 2 : ℝ) by
        nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)])]
    rw [h3]
  have h4 : sqrt (41 + 24 * sqrt 2) = 4 * Real.sqrt 2 + 3 := by
    have h5 : (41 + 24 * sqrt 2 : ℝ) = (4 * Real.sqrt 2 + 3) ^ 2 := by
      nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    rw [h5]
    have h6 : sqrt ((4 * Real.sqrt 2 + 3) ^ 2) = 4 * Real.sqrt 2 + 3 := by
      rw [Real.sqrt_sq (show 0 ≤ (4 * Real.sqrt 2 + 3 : ℝ) by
        nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)])]
    rw [h6]
  rw [h1, h4]
  nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]