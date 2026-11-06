import Mathlib

open Real Set
open scoped Real

theorem algebra_285831 : 100 * (sin (253 * π / 180) * sin (313 * π / 180) +
    sin (163 * π / 180) * sin (223 * π / 180)) = 50 := by

  have h1 : sin (253 * π / 180) = - sin (73 * π / 180) := by 
    have h2 : 253 * π / 180 = π + 73 * π / 180 := by
      ring
    rw [h2]
    have h3 : sin (π + 73 * π / 180) = - sin (73 * π / 180) := by
      rw [sin_add, sin_pi, cos_pi]
      ring
    exact h3

  have h2 : sin (313 * π / 180) = - sin (47 * π / 180) := by
    have h3 : 313 * π / 180 = 2 * π - 47 * π / 180 := by
      ring
    rw [h3]
    have h4 : sin (2 * π - 47 * π / 180) = - sin (47 * π / 180) := by
      rw [sin_two_pi_sub]
    exact h4

  have h3 : sin (163 * π / 180) = cos (73 * π / 180) := by
    have h4 : 163 * π / 180 = π / 2 + 73 * π / 180 := by
      ring
    rw [h4]
    have h5 : sin (π / 2 + 73 * π / 180) = cos (73 * π / 180) := by
      rw [sin_add, sin_pi_div_two, cos_pi_div_two]
      ring
    exact h5

  have h4 : sin (223 * π / 180) = - sin (43 * π / 180) := by
    have h5 : 223 * π / 180 = π + 43 * π / 180 := by
      ring
    rw [h5]
    have h6 : sin (π + 43 * π / 180) = - sin (43 * π / 180) := by
      rw [sin_add, sin_pi, cos_pi]
      ring
    exact h6

  rw [h1, h2, h3, h4]

  have h6 : sin (73 * π / 180) * sin (47 * π / 180) - cos (73 * π / 180) * sin (43 * π / 180) = 1 / 2 := by

    have h1 : sin (73 * π / 180) * sin (47 * π / 180) = (1 / 2) * (cos (73 * π / 180 - 47 * π / 180) - cos (73 * π / 180 + 47 * π / 180)) := by 
      rw [cos_sub, cos_add]
      ring

    have h2 : cos (73 * π / 180) * sin (43 * π / 180) = (1 / 2) * (sin (73 * π / 180 + 43 * π / 180) + sin (43 * π / 180 - 73 * π / 180)) := by
      rw [sin_add, sin_sub]
      ring

    rw [h1, h2]

    have h3 : cos (73 * π / 180 - 47 * π / 180) = cos (26 * π / 180) := by ring_nf

    have h4 : cos (73 * π / 180 + 47 * π / 180) = cos (120 * π / 180) := by ring_nf

    have h5 : sin (73 * π / 180 + 43 * π / 180) = sin (116 * π / 180) := by ring_nf

    have h6 : sin (43 * π / 180 - 73 * π / 180) = sin (- (30 * π / 180)) := by ring_nf

    rw [h3, h4, h5, h6]

    have h7 : cos (120 * π / 180) = -1 / 2 := by 
      have h1 : 120 * π / 180 = π - π / 3 := by ring
      rw [h1]
      rw [cos_pi_sub]
      norm_num

    have h8 : sin (- (30 * π / 180)) = -1 / 2 := by 
      have h1 : 30 * π / 180 = π / 6 := by ring
      rw [h1]
      have h2 : sin (- (π / 6)) = - sin (π / 6) := by 
        rw [sin_neg]
      rw [h2]
      rw [sin_pi_div_six]
      all_goals norm_num

    have h9 : cos (26 * π / 180) = sin (64 * π / 180) := by 
      have h1 : 26 * π / 180 = π / 2 - 64 * π / 180 := by ring
      rw [h1]
      rw [cos_pi_div_two_sub]

    have h10 : sin (116 * π / 180) = sin (64 * π / 180) := by 
      have h1 : 116 * π / 180 = π - 64 * π / 180 := by ring
      rw [h1]
      rw [sin_pi_sub]

    rw [h7, h8, h9, h10]

    linarith

  have h5 : 100 * ((- sin (73 * π / 180)) * (- sin (47 * π / 180)) + cos (73 * π / 180) * (- sin (43 * π / 180))) = 100 * (sin (73 * π / 180) * sin (47 * π / 180) - cos (73 * π / 180) * sin (43 * π / 180)) := by ring
  rw [h5]
  rw [h6]
  all_goals norm_num