import Mathlib

open Real

theorem algebra_11981 : cos (75 * π / 180) ^ 2 + cos (15 * π / 180) ^ 2 + cos (75 * π / 180) * cos (15 * π / 180) = 5 / 4 := by
  have h1 : cos (75 * π / 180) = sin (15 * π / 180) := by
    have h2 : 75 * π / 180 = π / 2 - (15 * π / 180) := by 
      linarith [pi_pos]
    rw [h2]
    rw [cos_pi_div_two_sub]
  rw [h1]
  have h3 : sin (15 * π / 180) ^ 2 + cos (15 * π / 180) ^ 2 = 1 := by 
    have h4 : sin (15 * π / 180) ^ 2 + cos (15 * π / 180) ^ 2 = 1 := by 
      exact Real.sin_sq_add_cos_sq (15 * π / 180)
    linarith [h4]
  have h4 : sin (15 * π / 180) * cos (15 * π / 180) = (1 / 2) * sin (30 * π / 180) := by 
    have h5 : 30 * π / 180 = 2 * (15 * π / 180) := by 
      ring_nf
    rw [h5]
    have h6 : sin (2 * (15 * π / 180)) = 2 * sin (15 * π / 180) * cos (15 * π / 180) := by 
      rw [sin_two_mul]
    rw [h6]
    all_goals ring_nf
  have h5 : sin (30 * π / 180) = 1 / 2 := by 
    have h6 : 30 * π / 180 = π / 6 := by
      ring_nf
    rw [h6]
    rw [sin_pi_div_six]
  calc
    sin (15 * π / 180) ^ 2 + cos (15 * π / 180) ^ 2 + sin (15 * π / 180) * cos (15 * π / 180)
        = 1 + (sin (15 * π / 180) * cos (15 * π / 180)) := by
          linarith [h3]
    _ = 1 + ( (1 / 2) * sin (30 * π / 180) ) := by
      rw [h4]
      all_goals ring_nf
    _ = 1 + ( (1 / 2) * (1 / 2) ) := by 
      rw [h5]
      all_goals ring_nf
    _ = 5 / 4 := by 
      ring_nf