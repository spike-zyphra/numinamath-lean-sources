import Mathlib

open Real Set
open scoped Real

theorem algebra_113297 : (2 * cos (10 * π / 180) - sin (20 * π / 180)) / cos (20 * π / 180) = sqrt 3 := by
  have h1 : 2 * cos (10 * π / 180) - sin (20 * π / 180) = Real.sqrt 3 * cos (20 * π / 180) := by
    have h2 : cos (10 * π / 180) = cos (π / 6 - (20 * π / 180)) := by
      ring_nf
    rw [h2]
    have h3 : cos (π / 6 - (20 * π / 180)) = cos (π / 6) * cos (20 * π / 180) + sin (π / 6) * sin (20 * π / 180) := by 
      rw [cos_sub]
    rw [h3]
    have h4 : cos (π / 6) = Real.sqrt 3 / 2 := by 
      rw [cos_pi_div_six]
    have h5 : sin (π / 6) = 1 / 2 := by 
      rw [sin_pi_div_six]
    rw [h4, h5]
    linarith 
  have h2 : cos (20 * π / 180) ≠ 0 := by
    have h1 : 0 < 20 * π / 180 := by
      have h3 : 0 < π := Real.pi_pos
      linarith [Real.pi_pos]
    have h4 : cos (20 * π / 180) > 0 := by
      apply cos_pos_of_mem_Ioo
      constructor
      · linarith [Real.pi_pos]
      · linarith [Real.pi_pos]
    linarith 
  rw [h1]
  field_simp [h2]