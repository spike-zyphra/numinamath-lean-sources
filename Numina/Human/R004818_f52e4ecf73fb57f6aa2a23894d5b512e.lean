import Mathlib

open Real

theorem algebra_550215 : (2 * sin (25 * π / 180) ^ 2 - 1) / (sin (20 * π / 180) * cos (20 * π / 180)) = -2 := by
  have h1 : cos (25 * π / 180) ^ 2 = (1 + cos (50 * π / 180)) / 2 := by
    have h : cos (25 * π / 180) ^ 2 = (1 + cos (2 * (25 * π / 180))) / 2 := by
      rw [cos_sq]
      ring
    rw [h]
    ring_nf
  
  have h2 : 2 * sin (25 * π / 180) ^ 2 - 1 = -cos (50 * π / 180) := by
    have hsin_sq : sin (25 * π / 180) ^ 2 = 1 - cos (25 * π / 180) ^ 2 := by
      rw [← sin_sq_add_cos_sq (25 * π / 180)]
      linarith
    rw [hsin_sq, h1]
    linarith

  have h3 : sin (20 * π / 180) * cos (20 * π / 180) = (1 / 2) * sin (40 * π / 180) := by
    have h : sin (40 * π / 180) = 2 * sin (20 * π / 180) * cos (20 * π / 180) := by
      rw [show 40 * π / 180 = 2 * (20 * π / 180) by ring]
      rw [sin_two_mul]
    linarith

  have h4 : sin (40 * π / 180) = cos (50 * π / 180) := by
    have h : sin (40 * π / 180) = sin (π / 2 - (50 * π / 180)) := by
      ring_nf
    rw [h]
    rw [sin_pi_div_two_sub]

  rw [h2, h3, h4]
  
  have h5 : cos (50 * π / 180) ≠ 0 := by 
    have hpos : 0 < cos (50 * π / 180) := by
      apply cos_pos_of_mem_Ioo
      constructor
      · linarith [pi_pos]
      · linarith [pi_pos]
    linarith
  
  field_simp [h5]
  ring