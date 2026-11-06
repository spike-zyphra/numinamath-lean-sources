import Mathlib

open Real

theorem algebra_300974 : (12 - 2 * sqrt 35 + sqrt 14 + sqrt 10) / (sqrt 7 - sqrt 5 + sqrt 2) = 2 * sqrt 7 - sqrt 2 := by
  have h1 : sqrt 35 = sqrt 5 * sqrt 7 := by
    rw [sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  have h2 : sqrt 14 = sqrt 2 * sqrt 7 := by
    rw [sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  have h3 : sqrt 10 = sqrt 2 * sqrt 5 := by
    rw [sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  have h4 : 12 - 2 * sqrt 35 + sqrt 14 + sqrt 10 = (sqrt 7 - sqrt 5) ^ 2 + sqrt 2 * (sqrt 7 + sqrt 5) := by
    rw [h1, h2, h3]
    nlinarith [Real.sqrt_nonneg 5, Real.sqrt_nonneg 7, Real.sqrt_nonneg 2, sq_nonneg (sqrt 5 - sqrt 7), sq_nonneg (sqrt 2), Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (7 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), mul_nonneg (Real.sqrt_nonneg 5) (Real.sqrt_nonneg 7)]
  have h6 : sqrt 7 - sqrt 5 + sqrt 2 ≠ 0 := by
    nlinarith [Real.sqrt_nonneg 7, Real.sqrt_nonneg 5, Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (7: ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (5: ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (2: ℝ) by norm_num), sq_nonneg (sqrt 7 - sqrt 5), sq_nonneg (sqrt 7 - sqrt 2), sq_nonneg (sqrt 5 - sqrt 2), Real.sqrt_pos.mpr (show (0 : ℝ) < 7 by norm_num : (7 : ℝ) > 0), Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num : (5 : ℝ) > 0), Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num : (2 : ℝ) > 0)]
  rw [h4]
  field_simp [h6]
  <;> nlinarith [Real.sqrt_nonneg 7, Real.sqrt_nonneg 5, Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (7: ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (5: ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (2: ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (35: ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (14: ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (10: ℝ) by norm_num), sq_nonneg (sqrt 7 - sqrt 5), sq_nonneg (sqrt 7 - sqrt 2), sq_nonneg (sqrt 5 - sqrt 2), Real.sqrt_pos.mpr (show (0 : ℝ) < 7 by norm_num : (7 : ℝ) > 0), Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num : (5 : ℝ) > 0), Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num : (2 : ℝ) > 0)]