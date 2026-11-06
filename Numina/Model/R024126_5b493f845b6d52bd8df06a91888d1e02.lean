import Mathlib

open Real

theorem algebra_313940 : cos (π / 7) - cos (2 * π / 7) + cos (3 * π / 7) = 1 / 2 := by

  have h1 : cos (3 * π / 7) = -cos (4 * π / 7) := by
    have h2 : 3 * π / 7 = π - 4 * π / 7 := by 
      linarith [Real.pi_pos]
    rw [h2]
    rw [cos_pi_sub]

  rw [h1]

  have h3 : sin (π / 7) > 0 := by 
    apply sin_pos_of_pos_of_lt_pi
    linarith [Real.pi_pos]
    linarith [Real.pi_pos]

  have h4 : (cos (π / 7) - cos (2 * π / 7) - cos (4 * π / 7)) * (2 * sin (π / 7)) = sin (π / 7) := by

    have h7 : 2 * sin (π / 7) * cos (π / 7) = sin (2 * π / 7) := by
      have h8 : sin (2 * π / 7) = 2 * sin (π / 7) * cos (π / 7) := by
        rw [show 2 * π / 7 = 2 * (π / 7) by ring]
        rw [sin_two_mul]
      linarith

    have h8 : 2 * sin (π / 7) * cos (2 * π / 7) = sin (3 * π / 7) - sin (π / 7) := by
      have h9 : 2 * sin (π / 7) * cos (2 * π / 7) = sin (π / 7 + 2 * π / 7) + sin (π / 7 - 2 * π / 7) := by
        rw [sin_add, sin_sub]
        ring
      rw [h9]
      have h10 : π / 7 + 2 * π / 7 = 3 * π / 7 := by ring
      have h11 : π / 7 - 2 * π / 7 = -(π / 7) := by ring
      rw [h10, h11]
      have h12 : sin (-(π / 7)) = -sin (π / 7) := by rw [sin_neg]
      rw [h12]
      all_goals ring

    have h13 : 2 * sin (π / 7) * cos (4 * π / 7) = sin (5 * π / 7) - sin (3 * π / 7) := by
      have h14 : 2 * sin (π / 7) * cos (4 * π / 7) = sin (π / 7 + 4 * π / 7) + sin (π / 7 - 4 * π / 7) := by
        rw [sin_add, sin_sub]
        ring
      rw [h14]
      have h15 : π / 7 + 4 * π / 7 = 5 * π / 7 := by ring
      have h16 : π / 7 - 4 * π / 7 = -(3 * π / 7) := by ring
      rw [h15, h16]
      have h17 : sin (-(3 * π / 7)) = -sin (3 * π / 7) := by rw [sin_neg]
      rw [h17]
      all_goals ring

    have h18 : sin (5 * π / 7) = sin (2 * π / 7) := by
      have h19 : 5 * π / 7 = π - 2 * π / 7 := by ring
      rw [h19]
      rw [sin_pi_sub]

    rw [show (cos (π / 7) - cos (2 * π / 7) - cos (4 * π / 7)) * (2 * sin (π / 7)) = 
      2 * sin (π / 7) * cos (π / 7) - (2 * sin (π / 7) * cos (2 * π / 7)) - (2 * sin (π / 7) * cos (4 * π / 7)) by ring]

    rw [h7, h8, h13, h18]
    ring

  have h12 : sin (π / 7) ≠ 0 := by
    have h73 : sin (π / 7) > 0 := h3
    linarith

  have h14 : cos (π / 7) - cos (2 * π / 7) - cos (4 * π / 7) = 1 / 2 := by 
    apply (mul_left_inj' h12).mp
    linarith

  linarith