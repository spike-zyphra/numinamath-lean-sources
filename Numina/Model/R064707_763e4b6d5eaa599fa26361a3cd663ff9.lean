import Mathlib

open Real

theorem algebra_6383 : cos (75 * π / 180) = (Real.sqrt 6 - Real.sqrt 2) / 4 := by 
  have h1 : 75 * π / 180 = π / 4 + π / 6 := by 
    linarith [pi_pos]
  rw [h1]
  rw [cos_add]
  have h2 : cos (π / 4) = Real.sqrt 2 / 2 := by 
    rw [cos_pi_div_four]
  have h3 : sin (π / 4) = Real.sqrt 2 / 2 := by 
    rw [sin_pi_div_four]
  have h4 : cos (π / 6) = Real.sqrt 3 / 2 := by 
    rw [cos_pi_div_six]
  have h5 : sin (π / 6) = 1 / 2 := by 
    rw [sin_pi_div_six]
  rw [h2, h3, h4, h5]
  have h6 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by
    rw [show Real.sqrt 6 = Real.sqrt (2 * 3) by norm_num]
    rw [Real.sqrt_mul (by norm_num)]
  -- Now we need to show that the left side equals the right side
  field_simp [h6]
  <;> ring_nf <;> norm_num
  <;> ring_nf
  <;> norm_num [Real.sqrt_sq, Real.mul_self_sqrt, Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)]
  <;> ring_nf <;> norm_num
  <;> ring_nf <;> norm_num
  <;> try { tauto }
  all_goals 
    try { nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sqrt_nonneg 6, Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)] }
    <;> try { nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sqrt_nonneg 6, Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)] }
    <;> nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg (3 : ℝ), 
                  Real.sqrt_nonneg (6 : ℝ), Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), 
                  Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num), 
                  Real.sqrt_pos.mpr (show 0 < (6 : ℝ) by norm_num), 
                  Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num), 
                  Real.mul_self_sqrt (show (0 : ℝ) ≤ 3 by norm_num), 
                  Real.mul_self_sqrt (show (0 : ℝ) ≤ 6 by norm_num), 
                  h6, 
                  Real.sqrt_le_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
                  Real.sqrt_le_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num) ]