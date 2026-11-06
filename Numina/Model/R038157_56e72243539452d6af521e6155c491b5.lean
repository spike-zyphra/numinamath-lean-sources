import Mathlib

open Real Set
open scoped Real

theorem algebra_12908 : sin (75 * π / 180) - tan (60 * π / 180) * cos (255 * π / 180) = sqrt 2 := by

  have htan : tan (60 * π / 180) = sqrt 3 := by
    have : 60 * π / 180 = π / 3 := by 
      linarith [Real.pi_pos]
    rw [this]
    rw [tan_pi_div_three]
  
  have hcos : cos (255 * π / 180) = - cos (75 * π / 180) := by
    have h1 : 255 * π / 180 = π + 75 * π / 180 := by 
      linarith [Real.pi_pos]
    rw [h1]
    have h2 : cos (π + 75 * π / 180) = - cos (75 * π / 180) := by 
      rw [cos_add, cos_pi, sin_pi]
      ring
    exact h2
  
  rw [htan, hcos]

  have h3 : 75 * π / 180 = (5 * π / 12) := by
    linarith [Real.pi_pos]
  
  rw [h3]

  have h4 : sin (5 * π / 12) + sqrt 3 * cos (5 * π / 12) = 2 * sin (5 * π / 12 + π / 3) := by
    rw [sin_add]
    have h5 : sin (5 * π / 12) = sin (5 * π / 12) := rfl
    have h6 : cos (5 * π / 12) = cos (5 * π / 12) := rfl
    rw [h5, h6]
    have h7 : cos (π / 3) = 1 / 2 := by
      exact cos_pi_div_three
    have h8 : sin (π / 3) = Real.sqrt 3 / 2 := by
      exact sin_pi_div_three
    simp only [h7, h8]
    ring
  
  have h5 : 5 * π / 12 + π / 3 = 3 * π / 4 := by 
    linarith [Real.pi_pos]

  have h6 : sin (5 * π / 12 + π / 3) = Real.sqrt 2 / 2 := by
    rw [h5]
    have h7 : sin (3 * π / 4) = Real.sqrt 2 / 2 := by
      have h8 : 3 * π / 4 = Real.pi - (Real.pi / 4) := by 
        linarith [Real.pi_pos]
      rw [h8]
      rw [sin_pi_sub]
      have h9 : sin (Real.pi / 4) = Real.sqrt 2 / 2 := by
        exact sin_pi_div_four
      linarith [h9]
    linarith [h7]

  have h7 : 2 * sin (5 * π / 12 + π / 3) = Real.sqrt 2 := by
    linarith [h6]

  linarith [h4, h7]