import Mathlib

open Real Set
open scoped Real

theorem algebra_165627 : sin (arcsin 0.4 + arcsin 0.5) * sin (arcsin 0.5 - arcsin 0.4) = 0.09 := by
  have h1 : sin (arcsin 0.4 + arcsin 0.5) = sin (arcsin 0.4) * cos (arcsin 0.5) + cos (arcsin 0.4) * sin (arcsin 0.5) := by
    rw [sin_add]
  have h2 : sin (arcsin 0.5 - arcsin 0.4) = sin (arcsin 0.5) * cos (arcsin 0.4) - cos (arcsin 0.5) * sin (arcsin 0.4) := by
    rw [sin_sub]
  have h3 : sin (arcsin 0.4) = 0.4 := by
    apply sin_arcsin
    all_goals norm_num
  have h4 : sin (arcsin 0.5) = 0.5 := by
    apply sin_arcsin
    all_goals norm_num
  have h5 : cos (arcsin 0.4) = Real.sqrt (1 - (0.4 : ℝ) ^ 2) := by
    rw [cos_arcsin]
  have h6 : cos (arcsin 0.5) = Real.sqrt (1 - (0.5 : ℝ) ^ 2) := by
    rw [cos_arcsin]
  rw [h1, h2, h3, h4, h5, h6]
  have h7 : (Real.sqrt (1 - (0.4 : ℝ) ^ 2)) ^ 2 = (1 - (0.4 : ℝ) ^ 2) := by
    rw [Real.sq_sqrt]
    all_goals norm_num
  have h8 : (Real.sqrt (1 - (0.5 : ℝ) ^ 2)) ^ 2 = (1 - (0.5 : ℝ) ^ 2) := by
    rw [Real.sq_sqrt]
    all_goals norm_num
  nlinarith [Real.sqrt_nonneg (1 - (0.4 : ℝ) ^ 2), Real.sqrt_nonneg (1 - (0.5 : ℝ) ^ 2), h7, h8]