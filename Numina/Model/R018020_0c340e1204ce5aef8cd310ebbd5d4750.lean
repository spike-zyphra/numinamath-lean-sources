import Mathlib

open Real

theorem algebra_116115 : cos (π/7) * cos (2*π/7) * cos (3*π/7) = 1/8 := by

  have h2 : sin (8 * (π / 7)) = 8 * sin (π / 7) * cos (π / 7) * cos (2 * π / 7) * cos (4 * π / 7) := by
    have h1 : sin (8 * (π / 7)) = 2 * sin (4 * (π / 7)) * cos (4 * (π / 7)) := by
      rw [show 8 * (π / 7) = 2 * (4 * (π / 7)) by ring]
      rw [sin_two_mul]
    have h2 : sin (4 * (π / 7)) = 2 * sin (2 * (π / 7)) * cos (2 * (π / 7)) := by
      rw [show 4 * (π / 7) = 2 * (2 * (π / 7)) by ring]
      rw [sin_two_mul]
    have h3 : sin (2 * (π / 7)) = 2 * sin (π / 7) * cos (π / 7) := by
      rw [sin_two_mul]
    rw [h1, h2, h3]
    ring

  have h3 : sin (8 * (π / 7)) = - sin (π / 7) := by
    have h1 : 8 * (π / 7) = π + (π / 7) := by
      linarith [Real.pi_pos]
    rw [h1]
    have h2 : sin (π + (π / 7)) = - sin (π / 7) := by
      rw [sin_add, sin_pi, cos_pi]
      ring
    exact h2

  have h4 : sin (π / 7) ≠ 0 := by
    apply ne_of_gt
    apply sin_pos_of_pos_of_lt_pi
    linarith [Real.pi_pos]
    linarith [Real.pi_pos]

  have h5 : - sin (π / 7) = 8 * sin (π / 7) * cos (π / 7) * cos (2 * π / 7) * cos (4 * π / 7) := by
    linarith [h2, h3]

  have h6 : -1 / 8 = cos (π / 7) * cos (2 * π / 7) * cos (4 * π / 7) := by
    apply (mul_left_inj' h4).mp
    linarith

  have h7 : cos (4 * π / 7) = - cos (3 * π / 7) := by 
    have h1 : 4 * π / 7 = Real.pi - (3 * π / 7) := by 
      linarith [Real.pi_pos]
    rw [h1]
    have h2 : cos (Real.pi - (3 * π / 7)) = - cos (3 * π / 7) := by 
      rw [cos_pi_sub]
    exact h2

  rw [h7] at h6

  nlinarith