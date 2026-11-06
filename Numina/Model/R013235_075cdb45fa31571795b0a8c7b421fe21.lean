import Mathlib

open Real Set
open scoped Real

theorem algebra_208637 : cos (10 * π / 180) ^ 2 + cos (50 * π / 180) ^ 2 -
    sin (40 * π / 180) * sin (80 * π / 180) = 3 / 4 := by
  have h1 : sin (40 * π / 180) = cos (50 * π / 180) := by
    have h2 : 40 * π / 180 = π / 2 - 50 * π / 180 := by
      ring_nf
      <;> linarith [Real.pi_pos]
    rw [h2]
    rw [sin_pi_div_two_sub]
  have h3 : sin (80 * π / 180) = cos (10 * π / 180) := by
    have h4 : 80 * π / 180 = π / 2 - 10 * π / 180 := by
      ring_nf
      <;> linarith [Real.pi_pos]
    rw [h4]
    rw [sin_pi_div_two_sub]
  have h5 : sin (40 * π / 180) * sin (80 * π / 180) = cos (50 * π / 180) * cos (10 * π / 180) := by
    rw [h1, h3]
  rw [h5]
  have h6 : cos (50 * π / 180) = 1 / 2 * cos (10 * π / 180) + Real.sqrt 3 / 2 * sin (10 * π / 180) := by
    have h7 : 50 * π / 180 = Real.pi / 3 - 10 * π / 180 := by
      ring_nf
      <;> linarith [Real.pi_pos]
    rw [h7]
    rw [cos_sub]
    rw [cos_pi_div_three, sin_pi_div_three]
    all_goals ring_nf
    <;> linarith [Real.pi_pos]
  rw [h6]
  have h8 : cos (10 * π / 180) ^ 2 + (1 / 2 * cos (10 * π / 180) + Real.sqrt 3 / 2 * sin (10 * π / 180)) ^ 2 - (1 / 2 * cos (10 * π / 180) + Real.sqrt 3 / 2 * sin (10 * π / 180)) * cos (10 * π / 180) = 
          3 / 4 * (cos (10 * π / 180) ^ 2 + sin (10 * π / 180) ^ 2) := by
    nlinarith [Real.sin_sq_add_cos_sq (10 * π / 180), Real.sin_sq_add_cos_sq (50 * π / 180), Real.sin_sq_add_cos_sq (80 * π / 180), Real.sqrt_pos.mpr (show (3:ℝ) > 0 by norm_num), Real.sq_sqrt (show (0:ℝ) ≤ (3:ℝ) by norm_num)]
  have h9 : cos (10 * π / 180) ^ 2 + sin (10 * π / 180) ^ 2 = 1 := by 
    exact Real.cos_sq_add_sin_sq (10 * π / 180)
  nlinarith [h8, h9, Real.sqrt_pos.mpr (show (3:ℝ) > 0 by norm_num), Real.sq_sqrt (show (0:ℝ) ≤ (3:ℝ) by norm_num)]