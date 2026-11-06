import Mathlib

open Real Set
open scoped Real

theorem algebra_161664 (α : ℝ) :
  (2 * cos (π / 6 - 2 * α) - sqrt 3 * sin (5 * π / 2 - 2 * α)) /
  (cos (9 * π / 2 - 2 * α) + 2 * cos (π / 6 + 2 * α)) = tan (2 * α) / sqrt 3 := by

  have h1 : sin (5 * π / 2 - 2 * α) = cos (2 * α) := by
    have h2 : 5 * π / 2 - 2 * α = π / 2 - 2 * α + 2 * π := by
      ring_nf
    rw [h2]
    have h3 : sin (π / 2 - 2 * α + 2 * π) = sin (π / 2 - 2 * α) := by 
      rw [sin_add_two_pi]
    rw [h3]
    have h4 : sin (π / 2 - 2 * α) = cos (2 * α) := by 
      rw [sin_pi_div_two_sub]
    exact h4

  have h2 : cos (9 * π / 2 - 2 * α) = sin (2 * α) := by 
    have h3 : 9 * π / 2 - 2 * α = π / 2 - 2 * α + 4 * π := by
      ring_nf
    rw [h3]
    have h4 : cos (π / 2 - 2 * α + 4 * π) = cos (π / 2 - 2 * α) := by 
      have h5 : cos (π / 2 - 2 * α + 4 * π) = cos (π / 2 - 2 * α + 2 * π + 2 * π) := by 
        ring_nf
      rw [h5]
      have h6 : cos (π / 2 - 2 * α + 2 * π + 2 * π) = cos (π / 2 - 2 * α + 2 * π) := by 
        rw [cos_add_two_pi]
      have h7 : cos (π / 2 - 2 * α + 2 * π) = cos (π / 2 - 2 * α) := by 
        rw [cos_add_two_pi]
      rw [h6, h7]
    rw [h4]
    have h5 : cos (π / 2 - 2 * α) = sin (2 * α) := by 
      rw [cos_pi_div_two_sub]
    exact h5

  have h3 : cos (π / 6 - 2 * α) = Real.sqrt 3 / 2 * cos (2 * α) + 1 / 2 * sin (2 * α) := by
    rw [cos_sub]
    have h4 : cos (π / 6) = Real.sqrt 3 / 2 := by 
      exact cos_pi_div_six
    have h5 : sin (π / 6) = 1 / 2 := by 
      exact sin_pi_div_six
    simp [h4, h5]

  have h4 : cos (π / 6 + 2 * α) = Real.sqrt 3 / 2 * cos (2 * α) - 1 / 2 * sin (2 * α) := by 
    rw [cos_add]
    have h5 : cos (π / 6) = Real.sqrt 3 / 2 := by 
      exact cos_pi_div_six
    have h6 : sin (π / 6) = 1 / 2 := by 
      exact sin_pi_div_six
    simp [h5, h6]

  have h5 : 2 * cos (π / 6 - 2 * α) - Real.sqrt 3 * sin (5 * π / 2 - 2 * α) = sin (2 * α) := by 
    rw [h1, h3]
    ring

  have h6 : cos (9 * π / 2 - 2 * α) + 2 * cos (π / 6 + 2 * α) = Real.sqrt 3 * cos (2 * α) := by 
    rw [h2, h4]
    ring

  rw [h5, h6]
  have h7 : tan (2 * α) = sin (2 * α) / cos (2 * α) := by 
    rw [tan_eq_sin_div_cos]

  rw [h7]
  <;> field_simp <;> ring