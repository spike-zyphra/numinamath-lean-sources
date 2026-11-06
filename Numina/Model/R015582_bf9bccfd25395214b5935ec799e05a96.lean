import Mathlib

open Real

theorem algebra_159310 : cos (20 * π / 180) * cos (40 * π / 180) * cos (80 * π / 180) = 1 / 8 := by
  have h20 : cos (20 * π / 180) = cos (π / 9) := by
    ring_nf
  have h40 : cos (40 * π / 180) = cos (2 * π / 9) := by
    ring_nf
  have h80 : cos (80 * π / 180) = cos (4 * π / 9) := by
    ring_nf
  rw [h20, h40, h80]
  have h5 : sin (8 * (π / 9)) = 8 * sin (π / 9) * cos (π / 9) * cos (2 * π / 9) * cos (4 * π / 9) := by
    have h1 : sin (8 * (π / 9)) = 2 * sin (4 * (π / 9)) * cos (4 * (π / 9)) := by
      rw [show 8 * (π / 9) = 2 * (4 * (π / 9)) by ring]
      rw [sin_two_mul]
    have h2 : sin (4 * (π / 9)) = 2 * sin (2 * (π / 9)) * cos (2 * (π / 9)) := by
      rw [show 4 * (π / 9) = 2 * (2 * (π / 9)) by ring]
      rw [sin_two_mul]
    have h3 : sin (2 * (π / 9)) = 2 * sin (π / 9) * cos (π / 9) := by
      rw [sin_two_mul]
    rw [h1, h2, h3]
    ring
  have h6 : sin (8 * (π / 9)) = sin (π / 9) := by
    have h7 : 8 * (π / 9) = Real.pi - (π / 9) := by
      linarith [Real.pi_pos]
    rw [h7]
    rw [sin_pi_sub]
  have h7 : sin (π / 9) ≠ 0 := by
    have h8 : sin (π / 9) > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      linarith [Real.pi_pos]
      linarith [Real.pi_pos]
    linarith
  have h8 : cos (π / 9) * cos (2 * π / 9) * cos (4 * π / 9) = 1 / 8 := by
    have h8 : sin (8 * (π / 9)) = 8 * sin (π / 9) * (cos (π / 9) * cos (2 * π / 9) * cos (4 * π / 9)) := by
      linarith [h5]
    rw [h6] at h8
    apply (mul_left_inj' h7).mp
    linarith
  have h9 : cos (π / 9) * cos (2 * π / 9) * cos (4 * π / 9) = 1 / 8 := h8
  linarith