import Mathlib

open Real Set


theorem algebra_303070 : (sin (20 * π / 180))^3 - (sin (100 * π / 180))^3 + (sin (140 * π / 180))^3 = -3 * sqrt 3 / 8 := by

  have h1 : sin (20 * π / 180) = sin (π / 9) := by
    ring_nf

  have h2 : sin (100 * π / 180) = sin (5 * π / 9) := by
    ring_nf

  have h3 : sin (140 * π / 180) = sin (7 * π / 9) := by
    ring_nf

  rw [h1, h2, h3]

  have h4 : sin (π / 9) ^ 3 = (3 * sin (π / 9) - sin (3 * (π / 9))) / 4 := by
    have h7 : sin (3 * (π / 9)) = 3 * sin (π / 9) - 4 * sin (π / 9) ^ 3 := by
      rw [sin_three_mul]
    linarith

  have h5 : sin (5 * π / 9) ^ 3 = (3 * sin (5 * π / 9) - sin (3 * (5 * π / 9))) / 4 := by
    have h7 : sin (3 * (5 * π / 9)) = 3 * sin (5 * π / 9) - 4 * sin (5 * π / 9) ^ 3 := by
      rw [sin_three_mul]
    linarith

  have h6 : sin (7 * π / 9) ^ 3 = (3 * sin (7 * π / 9) - sin (3 * (7 * π / 9))) / 4 := by
    have h7 : sin (3 * (7 * π / 9)) = 3 * sin (7 * π / 9) - 4 * sin (7 * π / 9) ^ 3 := by
      rw [sin_three_mul]
    linarith

  rw [h4, h5, h6]

  have h7 : sin (3 * (π / 9)) = Real.sqrt 3 / 2 := by
    have h8 : 3 * (π / 9) = Real.pi / 3 := by
      linarith [Real.pi_pos]
    rw [h8]
    rw [sin_pi_div_three]

  have h8 : sin (3 * (5 * π / 9)) = - Real.sqrt 3 / 2 := by
    have h9 : 3 * (5 * π / 9) = 2 * Real.pi - (Real.pi / 3) := by
      linarith [Real.pi_pos]
    rw [h9]
    have h10 : sin (2 * Real.pi - (Real.pi / 3)) = - sin (Real.pi / 3) := by
      rw [sin_sub, sin_two_pi, cos_two_pi]
      norm_num
    rw [h10]
    rw [sin_pi_div_three]
    all_goals ring_nf

  have h9 : sin (3 * (7 * π / 9)) = Real.sqrt 3 / 2 := by
    have h10 : 3 * (7 * π / 9) = 2 * Real.pi + (Real.pi / 3) := by
      linarith [Real.pi_pos]
    rw [h10]
    have h11 : sin (2 * Real.pi + (Real.pi / 3)) = sin (Real.pi / 3) := by
      rw [sin_add, sin_two_pi, cos_two_pi]
      norm_num
    rw [h11]
    rw [sin_pi_div_three]

  rw [h7, h8, h9]

  have h10 : sin (π / 9) - sin (5 * π / 9) + sin (7 * π / 9) = 0 := by
    have h11 : sin (7 * π / 9) = sin (2 * π / 9) := by
      have h18 : 7 * π / 9 = Real.pi - (2 * π / 9) := by
        linarith [Real.pi_pos]
      rw [h18]
      rw [sin_pi_sub]

    have h12 : sin (5 * π / 9) = sin (4 * π / 9) := by
      have h18 : 5 * π / 9 = Real.pi - (4 * π / 9) := by
        linarith [Real.pi_pos]
      rw [h18]
      rw [sin_pi_sub]

    rw [h11, h12]

    have h13 : sin (π / 9) + sin (2 * π / 9) = cos (π / 18) := by
      have h14 : sin (π / 9) + sin (2 * π / 9) = 2 * sin ((π / 9 + 2 * π / 9) / 2) * cos ((π / 9 - 2 * π / 9) / 2) := by
        rw [show sin (π / 9) + sin (2 * π / 9) = 2 * sin ((π / 9 + 2 * π / 9) / 2) * cos ((π / 9 - 2 * π / 9) / 2) by
          rw [show π / 9 = (π / 9 + 2 * π / 9) / 2 + (π / 9 - 2 * π / 9) / 2 by ring]
          rw [show 2 * π / 9 = (π / 9 + 2 * π / 9) / 2 - (π / 9 - 2 * π / 9) / 2 by ring]
          rw [sin_add, sin_sub]
          ring_nf
        ]
      have h15 : (π / 9 + 2 * π / 9) / 2 = π / 6 := by
        linarith [Real.pi_pos]
      have h16 : (π / 9 - 2 * π / 9) / 2 = - (π / 18) := by
        linarith [Real.pi_pos]
      rw [h15, h16] at h14
      have h17 : cos (-(π / 18)) = cos (π / 18) := by
        rw [cos_neg]
      rw [h17] at h14
      have h18 : sin (π / 6) = 1 / 2 := by
        rw [sin_pi_div_six]
      rw [h18] at h14
      linarith [h14]

    have h14 : sin (4 * π / 9) = cos (π / 18) := by
      have h18 : 4 * π / 9 = Real.pi / 2 - (π / 18) := by
        linarith [Real.pi_pos]
      rw [h18]
      rw [sin_pi_div_two_sub]

    linarith [h13, h14]

  linarith [h10]