import Mathlib

open Real Set
open scoped Real

theorem algebra_178714 : (sin (160 * π / 180) + sin (40 * π / 180)) * (sin (140 * π / 180) + sin (20 * π / 180)) +
    (sin (50 * π / 180) - sin (70 * π / 180)) * (sin (130 * π / 180) - sin (110 * π / 180)) = 1 := by
  have h1 : sin (160 * π / 180) = sin (20 * π / 180) := by
    have h1 : 160 * π / 180 = π - 20 * π / 180 := by
      linarith [pi_pos]
    rw [h1]
    rw [sin_pi_sub]
  have h2 : sin (140 * π / 180) = sin (40 * π / 180) := by
    have h2 : 140 * π / 180 = π - 40 * π / 180 := by
      linarith [pi_pos]
    rw [h2]
    rw [sin_pi_sub]
  have h3 : sin (130 * π / 180) = sin (50 * π / 180) := by
    have h3 : 130 * π / 180 = π - 50 * π / 180 := by
      linarith [pi_pos]
    rw [h3]
    rw [sin_pi_sub]
  have h4 : sin (110 * π / 180) = sin (70 * π / 180) := by
    have h4 : 110 * π / 180 = π - 70 * π / 180 := by
      linarith [pi_pos]
    rw [h4]
    rw [sin_pi_sub]
  have h5 : sin (50 * π / 180) = cos (40 * π / 180) := by 
    have h5 : 50 * π / 180 = π / 2 - 40 * π / 180 := by 
      linarith [pi_pos]
    rw [h5]
    rw [sin_pi_div_two_sub]
  have h6 : sin (70 * π / 180) = cos (20 * π / 180) := by 
    have h6 : 70 * π / 180 = π / 2 - 20 * π / 180 := by 
      linarith [pi_pos]
    rw [h6]
    rw [sin_pi_div_two_sub]
  have h7 : sin (20 * π / 180) + sin (40 * π / 180) = cos (10 * π / 180) := by
    have h7 : sin (20 * π / 180) + sin (40 * π / 180) = 2 * sin (30 * π / 180) * cos (10 * π / 180) := by
      rw [show 20 * π / 180 = (30 * π / 180 - 10 * π / 180) by ring]
      rw [show 40 * π / 180 = (30 * π / 180 + 10 * π / 180) by ring]
      rw [sin_add, sin_sub]
      ring
    rw [h7]
    have h8 : sin (30 * π / 180) = 1 / 2 := by 
      have h9 : 30 * π / 180 = π / 6 := by 
        linarith [pi_pos]
      rw [h9]
      exact sin_pi_div_six
    rw [h8]
    ring
  have h9 : sin (40 * π / 180) + sin (20 * π / 180) = cos (10 * π / 180) := by 
    have h10 : sin (40 * π / 180) + sin (20 * π / 180) = 2 * sin (30 * π / 180) * cos (10 * π / 180) := by 
      rw [show 40 * π / 180 = (30 * π / 180 + 10 * π / 180) by ring]
      rw [show 20 * π / 180 = (30 * π / 180 - 10 * π / 180) by ring]
      rw [sin_add, sin_sub]
      ring
    rw [h10]
    have h11 : sin (30 * π / 180) = 1 / 2 := by 
      have h12 : 30 * π / 180 = π / 6 := by 
        linarith [pi_pos]
      rw [h12]
      exact sin_pi_div_six
    rw [h11]
    ring
  have h12 : cos (40 * π / 180) - cos (20 * π / 180) = -sin (10 * π / 180) := by 
    have h13 : cos (40 * π / 180) - cos (20 * π / 180) = -2 * sin (30 * π / 180) * sin (10 * π / 180) := by
      rw [show 40 * π / 180 = (30 * π / 180 + 10 * π / 180) by ring]
      rw [show 20 * π / 180 = (30 * π / 180 - 10 * π / 180) by ring]
      rw [cos_add, cos_sub]
      ring
    rw [h13]
    have h14 : sin (30 * π / 180) = 1 / 2 := by
      have h15 : 30 * π / 180 = π / 6 := by
        linarith [pi_pos]
      rw [h15]
      exact sin_pi_div_six
    rw [h14]
    ring
  rw [h1, h2, h3, h4, h5, h6]
  have h17 : (cos (10 * π / 180)) ^ 2 + (sin (10 * π / 180)) ^ 2 = 1 := by 
    exact Real.cos_sq_add_sin_sq (10 * π / 180)
  have h18 : (cos (40 * π / 180) - cos (20 * π / 180)) ^ 2 = (sin (10 * π / 180)) ^ 2 := by
    have h19 : cos (40 * π / 180) - cos (20 * π / 180) = -sin (10 * π / 180) := by
      exact h12
    rw [h19]
    ring
  rw [h7, h9]
  nlinarith [h17, h18]