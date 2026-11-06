import Mathlib

open Real

theorem calculus_23149 : sin (arcsin (4 / 10) + arcsin (5 / 10)) * sin (arcsin (5 / 10) - arcsin (4 / 10)) = 9 / 100 := by
  have h1 : sin (arcsin (4 / 10) + arcsin (5 / 10)) = sin (arcsin (4 / 10)) * cos (arcsin (5 / 10)) + cos (arcsin (4 / 10)) * sin (arcsin (5 / 10)) := by
    rw [sin_add]
  have h2 : sin (arcsin (5 / 10) - arcsin (4 / 10)) = sin (arcsin (5 / 10)) * cos (arcsin (4 / 10)) - cos (arcsin (5 / 10)) * sin (arcsin (4 / 10)) := by
    rw [sin_sub]
  have h3 : sin (arcsin (4 / 10 : ℝ)) = (4 / 10 : ℝ) := by 
    apply sin_arcsin
    all_goals linarith
  have h4 : sin (arcsin (5 / 10 : ℝ)) = (5 / 10 : ℝ) := by 
    apply sin_arcsin
    all_goals linarith
  have h5 : cos (arcsin (4 / 10 : ℝ)) = Real.sqrt (1 - (4 / 10 : ℝ) ^ 2) := by
    rw [cos_arcsin]
  have h6 : cos (arcsin (5 / 10 : ℝ)) = Real.sqrt (1 - (5 / 10 : ℝ) ^ 2) := by
    rw [cos_arcsin]
  rw [h1, h2, h3, h4, h5, h6]
  have h7 : Real.sqrt (1 - (4/10 : ℝ)^2) ^ 2 = 1 - (4/10 : ℝ) ^ 2 := by
    rw [Real.sq_sqrt]
    nlinarith
  have h8 : Real.sqrt (1 - (5/10 : ℝ)^2) ^ 2 = 1 - (5/10 : ℝ) ^ 2 := by
    rw [Real.sq_sqrt]
    nlinarith
  nlinarith [Real.sqrt_nonneg (1 - (4 / 10 : ℝ) ^ 2), Real.sqrt_nonneg (1 - (5 / 10 : ℝ) ^ 2),
    Real.sq_sqrt (show (0 : ℝ) ≤ 1 - (4 / 10 : ℝ) ^ 2 by nlinarith),
    Real.sq_sqrt (show (0 : ℝ) ≤ 1 - (5 / 10 : ℝ) ^ 2 by nlinarith),
    mul_nonneg (Real.sqrt_nonneg (1 - (4 / 10 : ℝ) ^ 2)) (Real.sqrt_nonneg (1 - (5 / 10 : ℝ) ^ 2))]