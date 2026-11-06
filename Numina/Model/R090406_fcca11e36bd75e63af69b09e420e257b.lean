import Mathlib

open Real

theorem calculus_11525 : cos (75 * π / 180) = (sqrt 6 - sqrt 2) / 4 := by
  have h1 : 75 * π / 180 = π / 4 + π / 6 := by 
    linarith [Real.pi_pos]
  rw [h1]
  rw [cos_add]
  have h2 : cos (π / 4) = Real.sqrt 2 / 2 := by 
    rw [cos_pi_div_four]
  have h3 : sin (π / 4) = Real.sqrt 2 / 2 := by 
    rw [sin_pi_div_four]
  have h4 : cos (π / 6) = Real.sqrt 3 / 2 := by 
    exact cos_pi_div_six
  have h5 : sin (π / 6) = 1 / 2 := by 
    exact sin_pi_div_six
  rw [h2, h3, h4, h5]
  have h6 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by 
    calc 
      Real.sqrt 6 = Real.sqrt (2 * 3 : ℝ) := by norm_num 
      _ = Real.sqrt (2 : ℝ) * Real.sqrt (3 : ℝ) := by 
        rw [Real.sqrt_mul (by norm_num)]
  rw [h6]
  linarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]