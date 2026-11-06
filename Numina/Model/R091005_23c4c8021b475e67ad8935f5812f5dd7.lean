import Mathlib

open Real Set
open scoped Real

theorem algebra_163936 : (sin (20 * π / 180) * cos (10 * π / 180) +
    cos (160 * π / 180) * cos (100 * π / 180)) /
    (sin (21 * π / 180) * cos (9 * π / 180) + cos (159 * π / 180) * cos (99 * π / 180)) = 1 := by
  have h1 : cos (160 * π / 180) = - cos (20 * π / 180) := by
    have h1 : 160 * π / 180 = π - 20 * π / 180 := by ring
    rw [h1]
    rw [cos_pi_sub]
  
  have h2 : cos (100 * π / 180) = - sin (10 * π / 180) := by
    have h2 : 100 * π / 180 = π / 2 + 10 * π / 180 := by ring
    rw [h2]
    rw [cos_add]
    simp [cos_pi_div_two, sin_pi_div_two]
    all_goals linarith [pi_pos]

  have h3 : cos (159 * π / 180) = - cos (21 * π / 180) := by
    have h3 : 159 * π / 180 = π - 21 * π / 180 := by ring
    rw [h3]
    rw [cos_pi_sub]

  have h4 : cos (99 * π / 180) = - sin (9 * π / 180) := by
    have h4 : 99 * π / 180 = π / 2 + 9 * π / 180 := by ring
    rw [h4]
    rw [cos_add]
    simp [cos_pi_div_two, sin_pi_div_two]
    all_goals linarith [pi_pos]

  have num_eq : sin (20 * π / 180) * cos (10 * π / 180) + cos (160 * π / 180) * cos (100 * π / 180) = sin (π / 6) := by
    rw [h1, h2]
    have h5 : sin (20 * π / 180) * cos (10 * π / 180) + (-cos (20 * π / 180)) * (-sin (10 * π / 180)) = sin (20 * π / 180 + 10 * π / 180) := by 
      rw [sin_add]
      ring
    rw [h5]
    have h6 : 20 * π / 180 + 10 * π / 180 = π / 6 := by ring
    rw [h6]

  have denom_eq : sin (21 * π / 180) * cos (9 * π / 180) + cos (159 * π / 180) * cos (99 * π / 180) = sin (π / 6) := by 
    rw [h3, h4]
    have h7 : sin (21 * π / 180) * cos (9 * π / 180) + (-cos (21 * π / 180)) * (-sin (9 * π / 180)) = sin (21 * π / 180 + 9 * π / 180) := by 
      rw [sin_add]
      ring
    rw [h7]
    have h8 : 21 * π / 180 + 9 * π / 180 = π / 6 := by ring
    rw [h8]

  have sin_pi_div_6 : sin (π / 6) = 1 / 2 := by 
    rw [sin_pi_div_six]

  rw [num_eq, denom_eq, sin_pi_div_6]
  field_simp [sin_pi_div_6]