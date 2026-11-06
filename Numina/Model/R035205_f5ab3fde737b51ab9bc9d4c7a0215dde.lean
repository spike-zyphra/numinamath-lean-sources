import Mathlib

open Real

theorem algebra_168037 : cos (10 * π / 180) ^ 2 + cos (50 * π / 180) ^ 2 - sin (40 * π / 180) * sin (80 * π / 180) = 3 / 4 := by 
  have h1 : cos (50 * π / 180) = 1 / 2 * cos (10 * π / 180) + Real.sqrt 3 / 2 * sin (10 * π / 180) := by
    have h2 : 50 * π / 180 = Real.pi / 3 - 10 * π / 180 := by 
      linarith [Real.pi_pos]
    rw [h2]
    rw [cos_sub]
    simp [cos_pi_div_three, sin_pi_div_three]
    <;> ring
  have h2 : sin (40 * π / 180) = cos (50 * π / 180) := by 
    have h3 : 40 * π / 180 = Real.pi / 2 - 50 * π / 180 := by 
      linarith [Real.pi_pos]
    rw [h3]
    rw [sin_pi_div_two_sub]
  have h3 : sin (80 * π / 180) = cos (10 * π / 180) := by
    have h4 : 80 * π / 180 = Real.pi / 2 - 10 * π / 180 := by
      linarith [Real.pi_pos]
    rw [h4]
    rw [sin_pi_div_two_sub]
  rw [h2, h3, h1]
  have h4 : (cos (10 * π / 180) ) ^ 2 + ( (1 / 2 * cos (10 * π / 180) + Real.sqrt 3 / 2 * sin (10 * π / 180) ) ) ^ 2 - ( (1 / 2 * cos (10 * π / 180) + Real.sqrt 3 / 2 * sin (10 * π / 180) ) ) * (cos (10 * π / 180) ) = 3 / 4 * ( cos (10 * π / 180) ^ 2 + sin (10 * π / 180) ^ 2 ) := by
    nlinarith [ Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num : (3 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ) ), Real.sqrt_nonneg 3, sq_nonneg (cos (10 * π / 180) - Real.sqrt 3 * sin (10 * π / 180) ), sq_nonneg ( cos (10 * π / 180) - sin (10 * π / 180) ), Real.sin_sq_add_cos_sq (10 * π / 180) ]
  have h5 : cos (10 * π / 180) ^ 2 + sin (10 * π / 180) ^ 2 = 1 := by 
    have h6 : cos (10 * π / 180) ^ 2 + sin (10 * π / 180) ^ 2 = 1 := by 
      exact Real.cos_sq_add_sin_sq (10 * π / 180)
    linarith
  linarith [ h4, h5 ]