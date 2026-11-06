import Mathlib

open Real Set
open scoped Real

theorem calculus_22248 : (sin (13 * π / 180) + sin (47 * π / 180) + sin (73 * π / 180) + sin (107 * π / 180)) / cos (17 * π / 180) = 3 := by

  have h1 : sin (13 * π / 180) = cos (77 * π / 180) := by
    have h2 : 13 * π / 180 = π / 2 - 77 * π / 180 := by 
      linarith [pi_pos]
    rw [h2]
    rw [sin_pi_div_two_sub]

  have h2 : sin (47 * π / 180) = cos (43 * π / 180) := by
    have h3 : 47 * π / 180 = π / 2 - 43 * π / 180 := by 
      linarith [pi_pos]
    rw [h3]
    rw [sin_pi_div_two_sub]

  have h3 : sin (73 * π / 180) = cos (17 * π / 180) := by
    have h4 : 73 * π / 180 = π / 2 - 17 * π / 180 := by
      linarith [pi_pos]
    rw [h4]
    rw [sin_pi_div_two_sub]

  have h4 : sin (107 * π / 180) = cos (17 * π / 180) := by
    have h5 : 107 * π / 180 = π / 2 + 17 * π / 180 := by
      linarith [pi_pos]
    rw [h5]
    have h7 : sin (π / 2 + 17 * π / 180) = cos (17 * π / 180) := by
      rw [sin_add, sin_pi_div_two, cos_pi_div_two]
      ring
    linarith [h7]

  have h5 : sin (13 * π / 180) + sin (47 * π / 180) + sin (73 * π / 180) + sin (107 * π / 180) = 3 * cos (17 * π / 180) := by
    rw [h1, h2, h3, h4]
    have h8 : cos (77 * π / 180) + cos (43 * π / 180) = 2 * cos (60 * π / 180) * cos (17 * π / 180) := by 
      rw [show 77 * π / 180 = 60 * π / 180 + 17 * π / 180 by ring]
      rw [show 43 * π / 180 = 60 * π / 180 - 17 * π / 180 by ring]
      rw [cos_add, cos_sub]
      ring_nf

    have h6 : cos (60 * π / 180) = 1 / 2 := by
      have h7 : 60 * π / 180 = π / 3 := by
        ring_nf
      rw [h7]
      exact cos_pi_div_three

    have h77 : cos (77 * π / 180) + cos (43 * π / 180) = cos (17 * π / 180) := by
      rw [h8, h6]
      linarith

    linarith [h77]

  have hc : cos (17 * π / 180) ≠ 0 := by
    have hc1 : 0 < 17 * π / 180 := by
      nlinarith [pi_pos]
    have hc2 : cos (17 * π / 180) > 0 := by
      apply cos_pos_of_mem_Ioo
      constructor <;> linarith [pi_pos, hc1]
    linarith

  rw [h5]
  field_simp [hc]
  all_goals linarith