import Mathlib

open Real

theorem algebra_186120 : (sin (160 * π / 180) + sin (40 * π / 180)) * (sin (140 * π / 180) + sin (20 * π / 180)) +
    (sin (50 * π / 180) - sin (70 * π / 180)) * (sin (130 * π / 180) - sin (110 * π / 180)) = 1 := by
  have h1 : sin (160 * π / 180) + sin (40 * π / 180) = sin (100 * π / 180) := by
    have h2 : sin (160 * π / 180) + sin (40 * π / 180) = 2 * sin (100 * π / 180) * cos (60 * π / 180) := by 
      rw [show 160 * π / 180 = 100 * π / 180 + 60 * π / 180 by ring]
      rw [show 40 * π / 180 = 100 * π / 180 - 60 * π / 180 by ring]
      rw [sin_add, sin_sub]
      ring
    have h3 : cos (60 * π / 180) = 1 / 2 := by 
      have : 60 * π / 180 = π / 3 := by ring
      rw [this]
      exact cos_pi_div_three
    rw [h3] at h2
    linarith
  have h2 : sin (140 * π / 180) + sin (20 * π / 180) = sin (80 * π / 180) := by 
    have h3 : sin (140 * π / 180) + sin (20 * π / 180) = 2 * sin (80 * π / 180) * cos (60 * π / 180) := by
      rw [show 140 * π / 180 = 80 * π / 180 + 60 * π / 180 by ring]
      rw [show 20 * π / 180 = 80 * π / 180 - 60 * π / 180 by ring]
      rw [sin_add, sin_sub]
      ring
    have h4 : cos (60 * π / 180) = 1 / 2 := by
      have : 60 * π / 180 = π / 3 := by ring
      rw [this]
      exact cos_pi_div_three
    rw [h4] at h3
    linarith
  have h3 : sin (50 * π / 180) - sin (70 * π / 180) = - sin (10 * π / 180) := by 
    have h4 : sin (50 * π / 180) - sin (70 * π / 180) = 2 * cos (60 * π / 180) * sin ( (50 * π / 180 - 70 * π / 180) / 2 ) := by 
      rw [sin_sub_sin]
      ring
    have h5 : cos (60 * π / 180) = 1 / 2 := by 
      have : 60 * π / 180 = π / 3 := by ring
      rw [this]
      exact cos_pi_div_three
    have h6 : (50 * π / 180 - 70 * π / 180) / 2 = - (10 * π / 180) := by ring
    rw [h6, h5] at h4
    have h7 : sin (-(10 * π / 180)) = - sin (10 * π / 180) := by 
      rw [sin_neg]
    have h8 : 2 * (1 / 2 : ℝ) * sin (-(10 * π / 180)) = - sin (10 * π / 180) := by 
      rw [h7]
      ring
    linarith [h4, h8]
  have h4 : sin (130 * π / 180) - sin (110 * π / 180) = - sin (10 * π / 180) := by 
    have h5 : sin (130 * π / 180) - sin (110 * π / 180) = 2 * cos (120 * π / 180) * sin ( (130 * π / 180 - 110 * π / 180) / 2 ) := by 
      rw [sin_sub_sin]
      ring
    have h6 : cos (120 * π / 180) = - 1 / 2 := by
      have : 120 * π / 180 = π - π / 3 := by ring
      rw [this]
      rw [cos_pi_sub]
      norm_num
    have h7 : (130 * π / 180 - 110 * π / 180) / 2 = 10 * π / 180 := by ring
    rw [h7, h6] at h5
    linarith [h5]
  rw [h1, h2, h3, h4]
  have h5 : sin (100 * π / 180) = sin (80 * π / 180) := by 
    have : 100 * π / 180 = π - 80 * π / 180 := by ring
    rw [this]
    rw [sin_pi_sub]
  have h7 : sin (10 * π / 180) = cos (80 * π / 180) := by 
    have : 10 * π / 180 = π / 2 - 80 * π / 180 := by ring
    rw [this]
    rw [sin_pi_div_two_sub]
  rw [h5]
  have h8 : sin (80 * π / 180) ^ 2 + cos (80 * π / 180) ^ 2 = 1 := by 
    apply Real.sin_sq_add_cos_sq 
  have h9 : sin (10 * π / 180) ^ 2 = cos (80 * π / 180) ^ 2 := by 
    rw [h7]
  nlinarith [h8, h9]