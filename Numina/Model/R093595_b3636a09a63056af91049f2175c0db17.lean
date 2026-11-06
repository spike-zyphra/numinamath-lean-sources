import Mathlib

open Real

theorem algebra_328095 : (3 + 2 * sqrt 2 - sqrt 3 - sqrt 6) / (1 + sqrt 2 - sqrt 3) = 1 + sqrt 2 := by
  have h1 : 1 + sqrt 2 - sqrt 3 ≠ 0 := by
    by_contra h
    have h2 : sqrt 3 = 1 + sqrt 2 := by linarith
    have h3 : (sqrt 3 : ℝ) ^ 2 = (1 + sqrt 2) ^ 2 := by
      rw [h2]
    have h4 : (sqrt 3 : ℝ) ^ 2 = 3 := by
      exact sq_sqrt (show 0 ≤ 3 by norm_num)
    have h5 : (1 + sqrt 2 : ℝ) ^ 2 = 3 + 2 * sqrt 2 := by
      nlinarith [sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (2 : ℝ) > 0)]
  have h2 : 3 + 2 * sqrt 2 - sqrt 3 - sqrt 6 = (1 + sqrt 2) * (1 + sqrt 2 - sqrt 3) := by
    have h3 : sqrt 6 = sqrt 2 * sqrt 3 := by
      have h4 : (6 : ℝ) = 2 * 3 := by norm_num
      have h5 : sqrt 6 = sqrt (2 * 3) := by rw [h4]
      rw [h5]
      rw [Real.sqrt_mul (by norm_num)]
      all_goals norm_num
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), h3, Real.sqrt_nonneg 2, Real.sqrt_nonneg 3]
  field_simp [h1]
  nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (2 : ℝ) > 0), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num : (3 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]