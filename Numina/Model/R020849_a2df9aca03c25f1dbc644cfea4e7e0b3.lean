import Mathlib

open Real

theorem algebra_130260 : sin (130 * π / 180) ^ 2 + sin (70 * π / 180) * cos (80 * π / 180) = 3 / 4 := by
  have h1 : sin (130 * π / 180) = sin (50 * π / 180) := by 
    have h2 : 130 * π / 180 = Real.pi - 50 * π / 180 := by
      ring_nf
    rw [h2]
    rw [sin_pi_sub]
  
  have h3 : sin (70 * π / 180) = Real.cos (20 * π / 180) := by 
    have h4 : 70 * π / 180 = Real.pi / 2 - 20 * π / 180 := by
      ring_nf
    rw [h4]
    rw [sin_pi_div_two_sub]

  have h4 : cos (80 * π / 180) = Real.sin (10 * π / 180) := by
    have h5 : 80 * π / 180 = Real.pi / 2 - 10 * π / 180 := by
      ring_nf
    rw [h5]
    rw [cos_pi_div_two_sub]

  rw [h1, h3, h4]
  
  have h5 : sin (50 * π / 180) = Real.sin (60 * π / 180) * Real.cos (10 * π / 180) - Real.cos (60 * π / 180) * Real.sin (10 * π / 180) := by 
    have h5 : 50 * π / 180 = 60 * π / 180 - 10 * π / 180 := by
      ring_nf
    rw [h5]
    rw [sin_sub]
  
  have h7 : Real.sin (60 * π / 180) = Real.sqrt 3 / 2 := by 
    have h8 : 60 * π / 180 = Real.pi / 3 := by 
      ring_nf
    rw [h8]
    rw [sin_pi_div_three]

  have h8 : Real.cos (60 * π / 180) = 1 / 2 := by 
    have h9 : 60 * π / 180 = Real.pi / 3 := by
      ring_nf
    rw [h9]
    rw [cos_pi_div_three]

  have h9 : Real.cos (20 * π / 180) = Real.cos (30 * π / 180) * Real.cos (10 * π / 180) + Real.sin (30 * π / 180) * Real.sin (10 * π / 180) := by
    have h9 : 20 * π / 180 = 30 * π / 180 - 10 * π / 180 := by 
      ring_nf
    rw [h9]
    rw [cos_sub]

  have h11 : Real.cos (30 * π / 180) = Real.sqrt 3 / 2 := by 
    have h12 : 30 * π / 180 = Real.pi / 6 := by
      ring_nf
    rw [h12]
    rw [cos_pi_div_six]

  have h12 : Real.sin (30 * π / 180) = 1 / 2 := by 
    have h13 : 30 * π / 180 = Real.pi / 6 := by
      ring_nf
    rw [h13]
    rw [sin_pi_div_six]

  rw [h5, h7, h8, h9, h11, h12]
  have h13 : Real.sin (10 * π / 180) ^ 2 + Real.cos (10 * π / 180) ^ 2 = 1 := by 
    have h14 : Real.sin (10 * π / 180) ^ 2 + Real.cos (10 * π / 180) ^ 2 = 1 := by 
      exact Real.sin_sq_add_cos_sq (10 * π / 180)
    linarith

  nlinarith [Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), sq_nonneg (Real.sin (10 * π / 180) - Real.sqrt 3 * Real.cos (10 * π / 180)), sq_nonneg (Real.sqrt 3 * Real.sin (10 * π / 180) - Real.cos (10 * π / 180)), Real.sin_sq_add_cos_sq (10 * π / 180)]