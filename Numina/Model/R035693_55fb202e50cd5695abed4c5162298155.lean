import Mathlib

open Real

theorem algebra_195907 : cos (π / 9) * cos (2 * π / 9) * cos (3 * π / 9) * cos (4 * π / 9) = 1 / 16 := by
  have h1 : cos (3 * π / 9) = 1 / 2 := by
    have h2 : 3 * π / 9 = π / 3 := by
      nlinarith [pi_pos]
    rw [h2]
    exact cos_pi_div_three
  have h3 : cos (π / 9) * cos (2 * π / 9) * cos (4 * π / 9) = 1 / 8 := by
    have h4 : sin (8 * (π / 9)) = 8 * sin (π / 9) * cos (π / 9) * cos (2 * π / 9) * cos (4 * π / 9) := by 
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
    have h5 : sin (8 * (π / 9)) = sin (π - (π / 9)) := by
      ring_nf
    have h6 : sin (π - (π / 9)) = sin (π / 9) := by
      rw [sin_pi_sub]
    have h7 : sin (π / 9) ≠ 0 := by
      have h1 : 0 < π / 9 := by 
        nlinarith [Real.pi_pos]
      have h2 : sin (π / 9) > 0 := by
        apply sin_pos_of_pos_of_lt_pi
        all_goals 
          nlinarith [Real.pi_pos]
      linarith
    have h8 : cos (π / 9) * cos (2 * π / 9) * cos (4 * π / 9) = 1 / 8 := by
      have h9 : sin (π / 9) ≠ 0 := h7
      have h8 : cos (π / 9) * cos (2 * π / 9) * cos (4 * π / 9) = 1 / 8 := by
        have h4' : sin (π / 9) = 8 * sin (π / 9) * cos (π / 9) * cos (2 * π / 9) * cos (4 * π / 9) := by
          have h9 : sin (8 * (π / 9)) = sin (π / 9) := by
            rw [h5, h6]
          linarith [h4, h9]
        have h10 : sin (π / 9) ≠ 0 := h7
        have h11 : cos (π / 9) * cos (2 * π / 9) * cos (4 * π / 9) = 1 / 8 := by
          apply (mul_left_inj' h10).mp
          linarith
        linarith
      linarith
    linarith
  rw [h1]
  calc
    cos (π / 9) * cos (2 * π / 9) * (1 / 2) * cos (4 * π / 9)
      = cos (π / 9) * cos (2 * π / 9) * cos (4 * π / 9) * (1 / 2) := by ring
    _ = (1 / 8) * (1 / 2) := by rw [h3]
    _ = 1 / 16 := by norm_num