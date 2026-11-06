import Mathlib

open Real Set
open scoped Real

theorem algebra_290642 : (cos (10 * π / 180))^2 + (cos (50 * π / 180))^2 -
    (sin (40 * π / 180)) * (sin (80 * π / 180)) = 3 / 4 := by
  have h1 : cos (50 * π / 180) = 1 / 2 * cos (10 * π / 180) + Real.sqrt 3 / 2 * sin (10 * π / 180) := by
    have h2 : 50 * π / 180 = Real.pi / 3 - 10 * π / 180 := by
      linarith [Real.pi_pos]
    rw [h2]
    rw [cos_sub]
    have h3 : cos (Real.pi / 3) = 1 / 2 := by
      rw [cos_pi_div_three]
    have h4 : sin (Real.pi / 3) = Real.sqrt 3 / 2 := by
      rw [sin_pi_div_three]
    rw [h3, h4]
    <;> ring
  have h2 : sin (40 * π / 180) = 1 / 2 * cos (10 * π / 180) + Real.sqrt 3 / 2 * sin (10 * π / 180) := by
    have h3 : 40 * π / 180 = Real.pi / 6 + 10 * π / 180 := by
      linarith [Real.pi_pos]
    rw [h3]
    rw [sin_add]
    have h4 : sin (Real.pi / 6) = 1 / 2 := by
      rw [sin_pi_div_six]
    have h5 : cos (Real.pi / 6) = Real.sqrt 3 / 2 := by
      have h6 : cos (Real.pi / 6) = Real.sqrt 3 / 2 := by
        exact cos_pi_div_six
      linarith
    rw [h4, h5]
    <;> ring_nf
  have h3 : sin (80 * π / 180) = cos (10 * π / 180) := by
    have h4 : 80 * π / 180 = Real.pi / 2 - 10 * π / 180 := by
      linarith [Real.pi_pos]
    rw [h4]
    rw [sin_pi_div_two_sub]
  rw [h1, h2, h3]
  have h4 : cos (10 * π / 180) ^ 2 + sin (10 * π / 180) ^ 2 = 1 := by
    exact Real.cos_sq_add_sin_sq (10 * π / 180)
  nlinarith [Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by linarith : (3 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg (cos (10 * π / 180) - sin (10 * π / 180)), sq_nonneg (cos (10 * π / 180) + sin (10 * π / 180)), Real.sin_sq_add_cos_sq (10 * π / 180)]