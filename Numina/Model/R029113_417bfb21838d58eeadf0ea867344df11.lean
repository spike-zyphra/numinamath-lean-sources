import Mathlib

open Real Set
open scoped Real

theorem algebra_290951 : cos (2 * π / 7) * cos (4 * π / 7) * cos (6 * π / 7) = 1 / 8 := by 
  have h1 : cos (6 * π / 7) = -cos (π / 7) := by 
    have h2 : 6 * π / 7 = π - π / 7 := by 
      ring 
    rw [h2] 
    rw [cos_pi_sub]
  rw [h1] 
  have h2 : sin (π / 7) > 0 := by 
    apply sin_pos_of_pos_of_lt_pi
    linarith [Real.pi_pos]
    linarith [Real.pi_pos]
  have h3 : sin (2 * π / 7) = 2 * sin (π / 7) * cos (π / 7) := by 
    rw [show 2 * π / 7 = 2 * (π / 7) by ring]
    rw [sin_two_mul]
  have h4 : sin (4 * π / 7) = 2 * sin (2 * π / 7) * cos (2 * π / 7) := by
    rw [show 4 * π / 7 = 2 * (2 * π / 7) by ring]
    rw [sin_two_mul]
  have h5 : 8 * sin (π / 7) * cos (π / 7) * cos (2 * π / 7) * cos (4 * π / 7) = sin (8 * (π / 7)) := by 
    have h6a : sin (8 * (π / 7)) = 2 * sin (4 * π / 7) * cos (4 * π / 7) := by 
      rw [show 8 * (π / 7) = 2 * (4 * π / 7) by ring]
      rw [sin_two_mul]
    have h7a : sin (4 * π / 7) = 2 * sin (2 * π / 7) * cos (2 * π / 7) := by 
      rw [show 4 * π / 7 = 2 * (2 * π / 7) by ring]
      rw [sin_two_mul]
    have h8a : sin (2 * π / 7) = 2 * sin (π / 7) * cos (π / 7) := by 
      rw [show 2 * π / 7 = 2 * (π / 7) by ring]
      rw [sin_two_mul]
    rw [h6a, h7a, h8a]
    ring 
  have h5a : sin (8 * (π / 7)) = -sin (π / 7) := by 
    have h5b : 8 * (π / 7) = π + (π / 7) := by 
      ring_nf 
    rw [h5b] 
    have h5c : sin (π + (π / 7)) = -sin (π / 7) := by 
      rw [sin_add, sin_pi, cos_pi]
      all_goals ring 
    linarith [h5c] 
  have h5b : 8 * sin (π / 7) * cos (π / 7) * cos (2 * π / 7) * cos (4 * π / 7) = -sin (π / 7) := by 
    linarith [h5, h5a] 
  have h5c : sin (π / 7) ≠ 0 := by 
    linarith [Real.sin_pos_of_pos_of_lt_pi (show 0 < π / 7 by linarith [Real.pi_pos]) (show π / 7 < Real.pi by linarith [Real.pi_pos])]
  have h5d : 8 * cos (π / 7) * cos (2 * π / 7) * cos (4 * π / 7) = -1 := by 
    apply (mul_left_inj' h5c).mp 
    linarith [h5b] 
  have h5e : cos (π / 7) * cos (2 * π / 7) * cos (4 * π / 7) = -1 / 8 := by 
    linarith [h5d] 
  nlinarith [h5e]