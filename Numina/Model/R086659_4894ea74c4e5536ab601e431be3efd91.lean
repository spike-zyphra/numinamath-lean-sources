import Mathlib

open Real

theorem algebra_323954 : (cos (75 * π / 180))^2 + (cos (15 * π / 180))^2 + cos (75 * π / 180) * cos (15 * π / 180) = 5 / 4 := by
  have h2 : cos (75 * π / 180) = cos (π / 4) * cos (π / 6) - sin (π / 4) * sin (π / 6) := by
    have h75 : 75 * π / 180 = π / 4 + π / 6 := by
      ring_nf
      <;> linarith [pi_pos]
    rw [h75]
    rw [cos_add]
  have h3 : cos (15 * π / 180) = cos (π / 4) * cos (π / 6) + sin (π / 4) * sin (π / 6) := by
    have h15 : 15 * π / 180 = π / 4 - π / 6 := by
      ring_nf
      <;> linarith [pi_pos]
    rw [h15]
    rw [cos_sub]
  have h4 : cos (π / 4) = Real.sqrt 2 / 2 := by
    rw [cos_pi_div_four]
  have h5 : cos (π / 6) = Real.sqrt 3 / 2 := by
    rw [cos_pi_div_six]
  have h6 : sin (π / 4) = Real.sqrt 2 / 2 := by
    rw [sin_pi_div_four]
  have h7 : sin (π / 6) = 1 / 2 := by
    rw [sin_pi_div_six]
  rw [h2, h3]
  rw [h4, h5, h6, h7]
  nlinarith [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), 
          Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num),
          Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, 
          sq_nonneg (Real.sqrt 2), sq_nonneg (Real.sqrt 3),
          Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]