import Mathlib

open Real Set
open scoped Real

theorem calculus_16203 :
  (sin (18 * π / 180) * cos (12 * π / 180) + cos (162 * π / 180) * cos (102 * π / 180)) /
  (sin (22 * π / 180) * cos (8 * π / 180) + cos (158 * π / 180) * cos (98 * π / 180)) = 1 := by

  have num_eq : sin (18 * π / 180) * cos (12 * π / 180) + cos (162 * π / 180) * cos (102 * π / 180) = 1 / 2 := by

    have h1 : cos (162 * π / 180) = -cos (18 * π / 180) := by
      have h2 : 162 * π / 180 = π - 18 * π / 180 := by
        linarith [pi_pos]
      rw [h2]
      rw [cos_pi_sub]
      all_goals linarith

    have h3 : cos (102 * π / 180) = -sin (12 * π / 180) := by
      have h4 : 102 * π / 180 = π / 2 + 12 * π / 180 := by
        nlinarith [pi_pos]
      rw [h4]
      rw [cos_add]
      simp [sin_pi_div_two, cos_pi_div_two]
      all_goals linarith

    rw [h1, h3]

    have h5 : sin (18 * π / 180) * cos (12 * π / 180) + (-cos (18 * π / 180)) * (-sin (12 * π / 180)) = sin (18 * π / 180 + 12 * π / 180) := by
      rw [sin_add]
      ring

    rw [h5]

    have h6 : 18 * π / 180 + 12 * π / 180 = π / 6 := by
      linarith [pi_pos]

    rw [h6]

    have h7 : sin (π / 6) = 1 / 2 := by
      exact sin_pi_div_six

    rw [h7]

  have denom_eq : sin (22 * π / 180) * cos (8 * π / 180) + cos (158 * π / 180) * cos (98 * π / 180) = 1 / 2 := by

    have h1 : cos (158 * π / 180) = -cos (22 * π / 180) := by
      have h2 : 158 * π / 180 = π - 22 * π / 180 := by
        nlinarith [pi_pos]
      rw [h2]
      rw [cos_pi_sub]
      all_goals linarith

    have h3 : cos (98 * π / 180) = -sin (8 * π / 180) := by
      have h4 : 98 * π / 180 = π / 2 + 8 * π / 180 := by
        nlinarith [pi_pos]
      rw [h4]
      rw [cos_add]
      simp [sin_pi_div_two, cos_pi_div_two]
      all_goals linarith

    rw [h1, h3]

    have h5 : sin (22 * π / 180) * cos (8 * π / 180) + (-cos (22 * π / 180)) * (-sin (8 * π / 180)) = sin (22 * π / 180 + 8 * π / 180) := by
      rw [sin_add]
      ring

    rw [h5]

    have h6 : 22 * π / 180 + 8 * π / 180 = π / 6 := by
      nlinarith [pi_pos]

    rw [h6]

    have h7 : sin (π / 6) = 1 / 2 := by
      exact sin_pi_div_six

    rw [h7]

  rw [num_eq, denom_eq]
  norm_num