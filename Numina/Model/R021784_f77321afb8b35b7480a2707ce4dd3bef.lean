import Mathlib

open Real Set
open scoped Real

theorem calculus_22585 : cos (2 * π / 7) * cos (4 * π / 7) * cos (8 * π / 7) = 1 / 8 := by 
  have h1 : cos (8 * π / 7) = -cos (π / 7) := by 
    have h2 : 8 * π / 7 = π + (π / 7) := by
      ring_nf
    rw [h2]
    have h3 : cos (π + (π / 7)) = -cos (π / 7) := by 
      rw [cos_add, cos_pi, sin_pi]
      ring
    exact h3
  rw [h1]
  have h6 : cos (2 * π / 7) * cos (4 * π / 7) * (-cos (π / 7)) = 
      - (cos (π / 7) * cos (2 * π / 7) * cos (4 * π / 7)) := by 
    ring_nf
  rw [h6]
  have h2 : cos (π / 7) * cos (2 * π / 7) * cos (4 * π / 7) = -1 / 8 := by
    have h1 : sin (8 * (π / 7)) = 8 * sin (π / 7) * (cos (π / 7) * cos (2 * π / 7) * cos (4 * π / 7)) := by 
      have h2 : sin (8 * (π / 7)) = 2 * sin (4 * (π / 7)) * cos (4 * (π / 7)) := by 
        rw [show 8 * (π / 7) = 2 * (4 * (π / 7)) by ring_nf]
        rw [sin_two_mul]
      have h3 : sin (4 * (π / 7)) = 2 * sin (2 * (π / 7)) * cos (2 * (π / 7)) := by 
        rw [show 4 * (π / 7) = 2 * (2 * (π / 7)) by ring_nf]
        rw [sin_two_mul]
      have h4 : sin (2 * (π / 7)) = 2 * sin (π / 7) * cos (π / 7) := by 
        rw [sin_two_mul]
      rw [h2, h3, h4]
      ring_nf
    have h3 : sin (8 * (π / 7)) = -sin (π / 7) := by 
      have h4 : 8 * (π / 7) = π + (π / 7) := by 
        ring_nf
      rw [h4]
      have h5 : sin (π + (π / 7)) = -sin (π / 7) := by 
        rw [sin_add, cos_pi, sin_pi]
        ring
      linarith [h5]
    have h4 : sin (π / 7) ≠ 0 := by 
      apply ne_of_gt
      apply sin_pos_of_pos_of_lt_pi 
      · linarith [pi_pos]
      · linarith [pi_pos]
    rw [h3] at h1 
    have h5 : cos (π / 7) * cos (2 * π / 7) * cos (4 * π / 7) = -1 / 8 := by 
      apply (mul_left_inj' h4).mp 
      linarith 
    linarith [h5]
  linarith [h2]