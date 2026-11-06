import Mathlib

open Real Set
open scoped Real

  theorem algebra_185806 (α : ℝ) :
  sin (2 * α - 3 * π / 2) + cos (2 * α - 8 * π / 3) + cos (2 * π / 3 + 2 * α) = 0 := by

  have h1 : sin (2 * α - 3 * π / 2) = cos (2 * α) := by
    have h3 : sin (2 * α - 3 * π / 2) = sin (2 * α) * cos (3 * π / 2) - cos (2 * α) * sin (3 * π / 2) := by 
      rw [show 2 * α - 3 * π / 2 = 2 * α - (3 * π / 2) by ring]
      rw [sin_sub]
    
    have h4 : cos (3 * π / 2) = 0 := by
      have h5 : 3 * π / 2 = π + π / 2 := by ring
      rw [h5]
      rw [cos_add]
      norm_num [cos_pi, sin_pi, cos_pi_div_two, sin_pi_div_two]

    have h6 : sin (3 * π / 2) = -1 := by
      have h7 : 3 * π / 2 = π + π / 2 := by ring
      rw [h7]
      rw [sin_add]
      norm_num [cos_pi, sin_pi, cos_pi_div_two, sin_pi_div_two]

    rw [h4, h6] at h3
    linarith [h3]

  have h2 : cos (2 * α - 8 * π / 3) = cos (2 * α) * (-1 / 2) + sin (2 * α) * (Real.sqrt 3 / 2) := by
    have h8 : 2 * α - 8 * π / 3 = 2 * α - 2 * π / 3 - 2 * π := by ring_nf
    rw [h8]
    have h10 : cos (2 * α - 2 * π / 3 - 2 * π) = cos (2 * α - 2 * π / 3) := by
      rw [cos_sub_two_pi]
    
    rw [h10]
    
    have h11 : cos (2 * α - 2 * π / 3) = cos (2 * α) * cos (2 * π / 3) + sin (2 * α) * sin (2 * π / 3) := by
      rw [show 2 * α - 2 * π / 3 = 2 * α - (2 * π / 3) by ring]
      rw [cos_sub]
    
    rw [h11]
    
    have h12 : cos (2 * π / 3) = -1 / 2 := by
      have h13 : 2 * π / 3 = π - π / 3 := by ring_nf
      rw [h13]
      rw [cos_pi_sub]
      norm_num
    have h13 : sin (2 * π / 3) = Real.sqrt 3 / 2 := by
      have h14 : 2 * π / 3 = π - π / 3 := by ring_nf
      rw [h14]
      rw [sin_pi_sub]
      have h15 : sin (π / 3) = Real.sqrt 3 / 2 := sin_pi_div_three
      linarith

    rw [h12, h13]
  
  have h3 : cos (2 * π / 3 + 2 * α) = cos (2 * α) * (-1 / 2) - sin (2 * α) * (Real.sqrt 3 / 2) := by
    have h14 : cos (2 * π / 3 + 2 * α) = cos (2 * α) * cos (2 * π / 3) - sin (2 * α) * sin (2 * π / 3) := by
      rw [show 2 * π / 3 + 2 * α = 2 * α + (2 * π / 3) by ring]
      rw [cos_add]
    
    rw [h14]
    
    have h12 : cos (2 * π / 3) = -1 / 2 := by
      have h13 : 2 * π / 3 = π - π / 3 := by ring_nf
      rw [h13]
      rw [cos_pi_sub]
      norm_num
    have h13 : sin (2 * π / 3) = Real.sqrt 3 / 2 := by
      have h14 : 2 * π / 3 = π - π / 3 := by ring_nf
      rw [h14]
      rw [sin_pi_sub]
      have h15 : sin (π / 3) = Real.sqrt 3 / 2 := sin_pi_div_three
      linarith
    rw [h12, h13]
  
  rw [h1, h2, h3]
  ring