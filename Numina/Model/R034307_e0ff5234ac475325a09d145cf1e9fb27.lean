import Mathlib

open Real Set
open scoped Real

theorem calculus_15195 : (1 + cos (π / 8)) * (1 + cos (3 * π / 8)) * (1 + cos (5 * π / 8)) * (1 + cos (7 * π / 8)) = 1 / 8 := by

  have h1 : cos (5 * π / 8) = -cos (3 * π / 8) := by 
    have h2 : 5 * π / 8 = π - (3 * π / 8) := by ring
    rw [h2]
    rw [cos_pi_sub]

  have h2 : cos (7 * π / 8) = -cos (π / 8) := by 
    have h3 : 7 * π / 8 = π - (π / 8) := by ring
    rw [h3]
    rw [cos_pi_sub]

  rw [h1, h2]
  have h3 : (1 + cos (π / 8)) * (1 + cos (3 * π / 8)) * (1 + (-cos (3 * π / 8))) * (1 + (-cos (π / 8))) = 
          (1 - cos (π / 8) ^ 2) * (1 - cos (3 * π / 8) ^ 2) := by 
    ring_nf
  have h7 : (1 - cos (π / 8) ^ 2) * (1 - cos (3 * π / 8) ^ 2) = 1 / 8 := by
    have h4 : sin (π / 4) = Real.sqrt 2 / 2 := by 
      rw [sin_pi_div_four]
    have h5 : cos (π / 4) = Real.sqrt 2 / 2 := by 
      rw [cos_pi_div_four]
    have h6 : cos (3 * π / 4) = -Real.sqrt 2 / 2 := by 
      have h7 : 3 * π / 4 = π - (π / 4) := by ring
      rw [h7]
      rw [cos_pi_sub]
      rw [cos_pi_div_four]
      all_goals ring
    have h7' : sin (π / 8) ^ 2 = (1 - cos (π / 4)) / 2 := by
      have h9 : sin (π / 8) ^ 2 = (1 - cos (2 * (π / 8)) ) / 2 := by 
        rw [sin_sq_eq_half_sub]
        <;> ring_nf 
      have h10 : 2 * (π / 8) = π / 4 := by ring
      rw [h10] at h9
      linarith [h9]
    have h8 : sin (3 * π / 8) ^ 2 = (1 - cos (3 * π / 4)) / 2 := by 
      have h10 : sin (3 * π / 8) ^ 2 = (1 - cos (2 * (3 * π / 8)) ) / 2 := by 
        rw [sin_sq_eq_half_sub]
        <;> ring_nf 
      have h11 : 2 * (3 * π / 8) = 3 * π / 4 := by ring
      rw [h11] at h10 
      linarith [h10]

    calc 
      (1 - cos (π / 8) ^ 2) * (1 - cos (3 * π / 8) ^ 2) = sin (π / 8) ^ 2 * sin (3 * π / 8) ^ 2 := by 
        have h7' : 1 - cos (π / 8) ^ 2 = sin (π / 8) ^ 2 := by 
          linarith [sin_sq_add_cos_sq (π / 8)]
        have h8' : 1 - cos (3 * π / 8) ^ 2 = sin (3 * π / 8) ^ 2 := by 
          linarith [sin_sq_add_cos_sq (3 * π / 8)]
        rw [h7', h8']
      _ = ((1 - cos (π / 4)) / 2) * ((1 - cos (3 * π / 4)) / 2) := by 
        rw [h7', h8]
      _ = ((1 - cos (π / 4)) / 2) * ((1 - (-Real.sqrt 2 / 2)) / 2) := by
        rw [h6]
      _ = ((1 - (Real.sqrt 2 / 2)) / 2) * ((1 + Real.sqrt 2 / 2) / 2) := by
        rw [h5]
        all_goals ring_nf
      _ = (1 / 8 : ℝ) := by 
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num : (2 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
  
  rw [h3]
  linarith [h7]