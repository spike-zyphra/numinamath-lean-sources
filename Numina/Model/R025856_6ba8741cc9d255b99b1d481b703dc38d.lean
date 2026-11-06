import Mathlib

open Real

theorem algebra_215173 : cos (20 * π / 180) + cos (60 * π / 180) + cos (100 * π / 180) + cos (140 * π / 180) = 1 / 2 := by 
  have h1 : cos (100 * π / 180) + cos (140 * π / 180) = -cos (20 * π / 180) := by
    have h2 : 100 * π / 180 = (5 * π / 9) := by ring_nf
    have h3 : 140 * π / 180 = (7 * π / 9) := by ring_nf
    have h4 : 20 * π / 180 = (π / 9) := by ring_nf
    rw [h2, h3, h4]
    have h5 : cos (5 * π / 9) + cos (7 * π / 9) = 2 * cos (2 * π / 3) * cos (π / 9) := by 
      have h4 : 5 * π / 9 = (2 * π / 3 - π / 9) := by 
        linarith [pi_pos]
      have h5 : 7 * π / 9 = (2 * π / 3 + π / 9) := by 
        linarith [pi_pos]
      rw [h4, h5]
      have h1 : cos (2 * π / 3 - π / 9) = cos (2 * π / 3) * cos (π / 9) + sin (2 * π / 3) * sin (π / 9) := by 
        rw [cos_sub]
      have h2 : cos (2 * π / 3 + π / 9) = cos (2 * π / 3) * cos (π / 9) - sin (2 * π / 3) * sin (π / 9) := by 
        rw [cos_add]
      rw [h1, h2]
      ring
    have h6 : cos (2 * π / 3) = -1 / 2 := by
      have h7 : 2 * π / 3 = π - π / 3 := by 
        linarith [pi_pos]
      rw [h7]
      rw [cos_pi_sub]
      norm_num
    rw [h6] at h5
    linarith
  have h2 : cos (60 * π / 180) = 1 / 2 := by
    have h3 : 60 * π / 180 = π / 3 := by ring_nf
    rw [h3]
    exact cos_pi_div_three
  linarith [h1, h2]