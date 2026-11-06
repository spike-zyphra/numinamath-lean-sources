import Mathlib

open Real

theorem algebra_113206 : cos (π / 18)^2 + cos (5 * π / 18)^2 - sin (4 * π / 18) * sin (8 * π / 18) = 3 / 4 := by
  have h1 : sin (4 * π / 18) = cos (5 * π / 18) := by
    have h2 : 4 * π / 18 = Real.pi / 2 - 5 * π / 18 := by 
      nlinarith [Real.pi_pos]
    rw [h2]
    rw [sin_pi_div_two_sub]
  have h2 : sin (8 * π / 18) = cos (π / 18) := by
    have h3 : 8 * π / 18 = Real.pi / 2 - π / 18 := by
      nlinarith [Real.pi_pos]
    rw [h3]
    rw [sin_pi_div_two_sub]
  rw [h1, h2]
  have h4 : cos (5 * π / 18) = 1 / 2 * cos (π / 18) + Real.sqrt 3 / 2 * sin (π / 18) := by
    have h5 : 5 * π / 18 = Real.pi / 3 - π / 18 := by 
      ring_nf
    rw [h5]
    rw [cos_sub]
    have h6 : cos (Real.pi / 3) = 1 / 2 := by
      exact cos_pi_div_three
    have h7 : sin (Real.pi / 3) = Real.sqrt 3 / 2 := by
      exact sin_pi_div_three
    rw [h6, h7]
    <;> ring_nf
  rw [h4]
  have h8 : cos (π / 18) ^ 2 + sin (π / 18) ^ 2 = 1 := by
    exact Real.cos_sq_add_sin_sq (π / 18)
  nlinarith [Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), h8]