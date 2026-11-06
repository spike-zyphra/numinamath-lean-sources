import Mathlib

open Real

theorem algebra_288279 : sin (20 * π / 180) ^ 2 + cos (50 * π / 180) ^ 2 + sin (20 * π / 180) * cos (50 * π / 180) = 3 / 4 := by
  have h1 : cos (50 * π / 180) = cos (20 * π / 180 + π / 6) := by
    ring_nf
  have h2 : cos (20 * π / 180 + π / 6) = cos (20 * π / 180) * cos (π / 6) - sin (20 * π / 180) * sin (π / 6) := by
    rw [cos_add]
  have h3 : cos (π / 6) = Real.sqrt 3 / 2 := by
    exact cos_pi_div_six
  have h4 : sin (π / 6) = 1 / 2 := by 
    exact sin_pi_div_six
  rw [h1, h2, h3, h4]
  have h6 : sin (20 * π / 180) ^ 2 + cos (20 * π / 180) ^ 2 = 1 := by
    have h7 : sin (20 * π / 180) ^ 2 + cos (20 * π / 180) ^ 2 = 1 := by
      exact Real.sin_sq_add_cos_sq (20 * π / 180)
    linarith
  nlinarith [Real.sin_sq_add_cos_sq (20 * π / 180), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sin_sq_add_cos_sq (20 * π / 180)]