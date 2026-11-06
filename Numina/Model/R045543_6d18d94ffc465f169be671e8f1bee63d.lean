import Mathlib

open Real

theorem algebra_285863 : 256 * sin (π / 18) * sin (π / 6) * sin (5 * π / 18) * sin (7 * π / 18) = 16 := by
  have h1 : sin (π / 6) = 1 / 2 := by
    rw [sin_pi_div_six]
  have h3 : sin (π / 18) * sin (5 * π / 18) * sin (7 * π / 18) = 1 / 8 := by
    have h3a : sin (7 * π / 18) = cos (π / 9) := by
      have h3 : 7 * π / 18 = π / 2 - π / 9 := by
        linarith [Real.pi_pos]
      rw [h3]
      rw [sin_pi_div_two_sub]
    have h4 : sin (π / 18) * sin (5 * π / 18) * cos (π / 9) = 1 / 8 := by
      have h5 : sin (π / 18) * sin (5 * π / 18) = (1 / 2) * (cos (2 * π / 9) - 1 / 2) := by
        have h6 : sin (π / 18) * sin (5 * π / 18) = (1 / 2) * (cos (4 * π / 18) - cos (6 * π / 18)) := by
          have h7 : sin (π / 18) * sin (5 * π / 18) = (1 / 2) * (cos (5 * π / 18 - π / 18) - cos (5 * π / 18 + π / 18)) := by
            rw [cos_sub, cos_add]
            ring
          have h8 : 5 * π / 18 - π / 18 = 4 * π / 18 := by ring
          have h9 : 5 * π / 18 + π / 18 = 6 * π / 18 := by ring
          rw [h8, h9] at h7
          linarith
        have h10 : 4 * π / 18 = 2 * π / 9 := by ring
        have h11 : 6 * π / 18 = π / 3 := by ring
        rw [h10, h11] at h6
        have h12 : cos (π / 3) = 1 / 2 := by
          exact cos_pi_div_three
        rw [h12] at h6
        linarith
      have h7 : (sin (π / 18) * sin (5 * π / 18)) * cos (π / 9) = 1 / 8 := by
        rw [h5]
        have h8 : ( (1 / 2) * (cos (2 * π / 9) - 1 / 2) ) * cos (π / 9) = 1 / 8 := by
          have h9 : cos (2 * π / 9) * cos (π / 9) = (1 / 2) * (cos (3 * π / 9) + cos (π / 9)) := by
            have h10 : cos (2 * π / 9) * cos (π / 9) = (1 / 2) * (cos (2 * π / 9 + π / 9) + cos (2 * π / 9 - π / 9)) := by
              rw [cos_add_cos]
              all_goals ring
            have h11 : 2 * π / 9 + π / 9 = 3 * π / 9 := by ring
            have h12 : 2 * π / 9 - π / 9 = π / 9 := by ring
            rw [h11, h12] at h10
            linarith
          have h13 : cos (3 * π / 9) = 1 / 2 := by
            have h14 : 3 * π / 9 = π / 3 := by ring
            rw [h14]
            exact cos_pi_div_three
          rw [h13] at h9
          nlinarith [Real.cos_sq_add_sin_sq (π / 9), sq_nonneg (cos (π / 9) ^ 2 - 3 / 4), sq_nonneg (cos (π / 9) - 1 / 2), Real.sin_pos_of_pos_of_lt_pi (show 0 < π / 9 by linarith [Real.pi_pos] ) (show π / 9 < Real.pi by linarith [Real.pi_pos] ) ]
        linarith
      linarith
    rw [h3a] at *
    linarith
  calc
    256 * sin (π / 18) * sin (π / 6) * sin (5 * π / 18) * sin (7 * π / 18)
        = 256 * (sin (π / 18) * sin (5 * π / 18) * sin (7 * π / 18)) * (1 / 2) := by
          rw [show sin (π / 6) = 1 / 2 by linarith [h1]]
          all_goals ring
    _ = 256 * (1 / 8) * (1 / 2) := by
        rw [h3]
    _ = 16 := by
        ring