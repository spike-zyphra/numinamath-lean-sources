import Mathlib

open Real Set
open scoped Real

theorem algebra_153726 : 3 * sin (π / 3) - 2 * cos (π / 6) + 3 * tan (π / 3) - 4 / tan (π / 2) = 7 * sqrt 3 / 2 := by
  have h1 : sin (π / 3) = Real.sqrt 3 / 2 := by 
    exact sin_pi_div_three
  have h2 : cos (π / 6) = Real.sqrt 3 / 2 := by 
    exact cos_pi_div_six
  have h3 : tan (π / 3) = Real.sqrt 3 := by 
    have h4 : tan (π / 3) = sin (π / 3) / cos (π / 3) := by 
      rw [tan_eq_sin_div_cos]
    rw [h4, h1]
    have h5 : cos (π / 3) = 1 / 2 := by 
      exact cos_pi_div_three
    rw [h5]
    field_simp
    <;> nlinarith [Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num : (3 : ℝ) > (0 : ℝ)), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num : (3 : ℝ) ≥ 0)]
  have h7 : tan (π / 2) = 0 := by
    have h8 : tan (π / 2) = sin (π / 2) / cos (π / 2) := by
      rw [tan_eq_sin_div_cos]
    rw [h8]
    have h9 : cos (π / 2) = 0 := by
      exact cos_pi_div_two
    rw [h9]
    norm_num [sin_pi_div_two]
  have h8 : 4 / tan (π / 2) = 0 := by 
    rw [h7]
    norm_num
  rw [h8]
  rw [h1, h2, h3]
  field_simp
  <;> nlinarith [Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num : (3 : ℝ) > (0 : ℝ)), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num : (3 : ℝ) ≥ 0)]