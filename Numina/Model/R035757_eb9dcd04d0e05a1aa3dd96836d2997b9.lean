import Mathlib

open Real

theorem algebra_12123 : cos (2 * π / 7) * cos (4 * π / 7) * cos (6 * π / 7) = 1 / 8 := by 
  have h1 : cos (6 * π / 7) = -cos (π / 7) := by 
    have h1 : 6 * π / 7 = π - (π / 7) := by ring
    rw [h1]
    rw [cos_pi_sub]
  -- Rewrite the product using h1
  have h2 : cos (6 * π / 7) = -cos (π / 7) := h1
  -- First step is to write the product in terms of cos(π/7)
  -- The product is cos(2π/7)cos(4π/7)cos(6π/7) = cos(2π/7)cos(4π/7)(-cos(π/7))
  -- We need the identity for cos(π/7)cos(2π/7)cos(4π/7) = -1/8
  have h3 : sin (8 * (π / 7)) = - sin (π / 7) := by 
    have h4 : 8 * (π / 7) = π + (π / 7) := by ring
    rw [h4]
    have h5 : sin (π + (π / 7)) = - sin (π / 7) := by 
      rw [sin_add, sin_pi, cos_pi]
      ring
    linarith [h5]
  have h4 : sin (8 * (π / 7)) = 8 * sin (π / 7) * cos (π / 7) * cos (2 * π / 7) * cos (4 * π / 7) := by
    have h8 : sin (8 * (π / 7)) = 2 * sin (4 * (π / 7)) * cos (4 * (π / 7)) := by 
      rw [show 8 * (π / 7) = 2 * (4 * (π / 7)) by ring]
      rw [sin_two_mul]
    have h9 : sin (4 * (π / 7)) = 2 * sin (2 * (π / 7)) * cos (2 * (π / 7)) := by 
      rw [show 4 * (π / 7) = 2 * (2 * (π / 7)) by ring]
      rw [sin_two_mul]
    have h10 : sin (2 * (π / 7)) = 2 * sin (π / 7) * cos (π / 7) := by 
      rw [show 2 * (π / 7) = 2 * (π / 7) by ring]
      rw [sin_two_mul]
    rw [h8, h9, h10]
    ring_nf
  have h5 : sin (π / 7) ≠ 0 := by 
    apply ne_of_gt
    apply sin_pos_of_pos_of_lt_pi
    · linarith [pi_pos]
    · linarith [pi_pos]
  have h6 : cos (π / 7) * cos (2 * π / 7) * cos (4 * π / 7) = -1 / 8 := by
    have eq1 := h3
    rw [h4] at eq1
    apply (mul_left_inj' h5).mp
    linarith 
  calc 
    cos (2 * π / 7) * cos (4 * π / 7) * cos (6 * π / 7)
        = cos (2 * π / 7) * cos (4 * π / 7) * (-cos (π / 7)) := by rw [h1]
    _ = - (cos (π / 7) * cos (2 * π / 7) * cos (4 * π / 7)) := by ring
    _ = - (-1 / 8) := by rw [h6]
    _ = 1 / 8 := by norm_num