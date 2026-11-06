import Mathlib

open Real

theorem algebra_252598 : sin (π/14) * sin (3*π/14) * sin (5*π/14) = 1/8 := by
  have h1 : sin (5 * π / 14) = cos (π / 7) := by
    have h2 : 5 * π / 14 = π / 2 - π / 7 := by
      ring
    rw [h2]
    rw [sin_pi_div_two_sub]

  have h2 : sin (3 * π / 14) = cos (2 * π / 7) := by
    have h3 : 3 * π / 14 = π / 2 - 2 * π / 7 := by
      linarith [Real.pi_pos]
    rw [h3]
    rw [sin_pi_div_two_sub]

  have h3' : sin (π / 14) = cos (3 * π / 7) := by
    have h4 : π / 14 = π / 2 - 3 * π / 7 := by
      linarith [Real.pi_pos]
    rw [h4]
    rw [sin_pi_div_two_sub]

  rw [h1, h2, h3']
  have h4 : cos (3 * π / 7) = - cos (4 * π / 7) := by
    have h5 : 3 * π / 7 = π - 4 * π / 7 := by
      ring
    rw [h5]
    rw [cos_pi_sub]

  rw [h4]
  have h5 : cos (π / 7) * cos (2 * π / 7) * (- cos (4 * π / 7)) = 1 / 8 := by
    have h6 : cos (π / 7) * cos (2 * π / 7) * cos (4 * π / 7) = -1 / 8 := by
      have h7 : sin (8 * (π / 7)) = - sin (π / 7) := by
        have h7' : 8 * (π / 7) = π + π / 7 := by
          ring
        rw [h7']
        have h8 : sin (π + π / 7) = - sin (π / 7) := by
          rw [sin_add, sin_pi, cos_pi]
          ring
        linarith [h8]

      have h8 : sin (8 * (π / 7)) = 8 * sin (π / 7) * cos (π / 7) * cos (2 * π / 7) * cos (4 * π / 7) := by
        have h9 : sin (8 * (π / 7)) = 2 * sin (4 * (π / 7)) * cos (4 * (π / 7)) := by
          have h10 : 8 * (π / 7) = 2 * (4 * (π / 7)) := by ring
          rw [h10]
          rw [sin_two_mul]
        have h11 : sin (4 * (π / 7)) = 2 * sin (2 * (π / 7)) * cos (2 * (π / 7)) := by
          have h12 : 4 * (π / 7) = 2 * (2 * (π / 7)) := by ring
          rw [h12]
          rw [sin_two_mul]
        have h10 : sin (2 * (π / 7)) = 2 * sin (π / 7) * cos (π / 7) := by
          rw [show 2 * (π / 7) = 2 * (π / 7) by ring]
          rw [sin_two_mul]
        rw [h9, h11, h10]
        all_goals ring

      rw [h8] at h7
      have h10 : sin (π / 7) > 0 := by
        apply sin_pos_of_pos_of_lt_pi
        all_goals linarith [Real.pi_pos]
      have h11 : sin (π / 7) ≠ 0 := by
        linarith

      have h12 : cos (π / 7) * cos (2 * π / 7) * cos (4 * π / 7) = -1 / 8 := by
        apply (mul_left_inj' h11).mp
        linarith

      linarith [h12]

    calc
      cos (π / 7) * cos (2 * π / 7) * (- cos (4 * π / 7)) = - (cos (π / 7) * cos (2 * π / 7) * cos (4 * π / 7)) := by ring
      _ = - (-1 / 8) := by rw [h6]
      _ = 1 / 8 := by norm_num

  linarith [h5]