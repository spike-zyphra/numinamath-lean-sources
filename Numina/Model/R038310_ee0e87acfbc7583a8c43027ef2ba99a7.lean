import Mathlib

open Real Set
open scoped Real

theorem algebra_178714 : (sin (160 * π / 180) + sin (40 * π / 180)) * (sin (140 * π / 180) + sin (20 * π / 180)) +
    (sin (50 * π / 180) - sin (70 * π / 180)) * (sin (130 * π / 180) - sin (110 * π / 180)) = 1 := by
  have h1 : sin (160 * π / 180) = sin (20 * π / 180) := by 
    have h1 : 160 * π / 180 = π - 20 * π / 180 := by 
      linarith [Real.pi_pos]
    rw [h1]
    rw [sin_pi_sub]
  have h2 : sin (140 * π / 180) = sin (40 * π / 180) := by 
    have h1 : 140 * π / 180 = π - 40 * π / 180 := by 
      linarith [Real.pi_pos]
    rw [h1]
    rw [sin_pi_sub]
  have h3 : sin (130 * π / 180) = sin (50 * π / 180) := by 
    have h1 : 130 * π / 180 = π - 50 * π / 180 := by 
      linarith [Real.pi_pos]
    rw [h1]
    rw [sin_pi_sub]
  have h4 : sin (110 * π / 180) = sin (70 * π / 180) := by 
    have h1 : 110 * π / 180 = π - 70 * π / 180 := by 
      linarith [Real.pi_pos]
    rw [h1]
    rw [sin_pi_sub]
  have h5 : sin (20 * π / 180) + sin (40 * π / 180) = cos (10 * π / 180) := by 
    have h1 : sin (20 * π / 180) = sin (30 * π / 180 - 10 * π / 180) := by 
      ring_nf
    have h2 : sin (40 * π / 180) = sin (30 * π / 180 + 10 * π / 180) := by 
      ring_nf
    rw [h1, h2]
    have h3 : sin (30 * π / 180 - 10 * π / 180) = sin (30 * π / 180) * cos (10 * π / 180) - cos (30 * π / 180) * sin (10 * π / 180) := by 
      rw [sin_sub]
    have h4 : sin (30 * π / 180 + 10 * π / 180) = sin (30 * π / 180) * cos (10 * π / 180) + cos (30 * π / 180) * sin (10 * π / 180) := by 
      rw [sin_add]
    rw [h3, h4]
    have h5 : sin (30 * π / 180) = 1 / 2 := by
      have h1 : 30 * π / 180 = π / 6 := by 
        linarith [Real.pi_pos]
      rw [h1]
      exact sin_pi_div_six
    have h6 : cos (30 * π / 180) = Real.sqrt 3 / 2 := by 
      have h1 : 30 * π / 180 = π / 6 := by 
        linarith [Real.pi_pos]
      rw [h1]
      exact cos_pi_div_six
    rw [h5, h6]
    ring_nf
  have h6' : sin (50 * π / 180) - sin (70 * π / 180) = - sin (10 * π / 180) := by
    have h3 : sin (50 * π / 180) = sin (60 * π / 180 - 10 * π / 180) := by 
      ring_nf
    have h4 : sin (70 * π / 180) = sin (60 * π / 180 + 10 * π / 180) := by
      ring_nf
    rw [h3, h4]
    have h5 : sin (60 * π / 180 - 10 * π / 180) = sin (60 * π / 180) * cos (10 * π / 180) - cos (60 * π / 180) * sin (10 * π / 180) := by 
      rw [sin_sub]
    have h6 : sin (60 * π / 180 + 10 * π / 180) = sin (60 * π / 180) * cos (10 * π / 180) + cos (60 * π / 180) * sin (10 * π / 180) := by 
      rw [sin_add]
    rw [h5, h6]
    have h7 : sin (60 * π / 180) = Real.sqrt 3 / 2 := by 
      have h1 : 60 * π / 180 = π / 3 := by 
        linarith [Real.pi_pos]
      rw [h1]
      exact sin_pi_div_three
    have h8 : cos (60 * π / 180) = 1 / 2 := by
      have h1 : 60 * π / 180 = π / 3 := by 
        linarith [Real.pi_pos]
      rw [h1]
      exact cos_pi_div_three
    rw [h7, h8]
    ring_nf
  have eq1 : (sin (160 * π / 180) + sin (40 * π / 180)) * (sin (140 * π / 180) + sin (20 * π / 180)) = (cos (10 * π / 180)) ^ 2 := by 
    rw [h1, h2]
    have eq2 : (sin (20 * π / 180) + sin (40 * π / 180)) * (sin (40 * π / 180) + sin (20 * π / 180)) = (sin (20 * π / 180) + sin (40 * π / 180)) ^ 2 := by 
      ring 
    rw [eq2]
    rw [h5]
  have eq2 : (sin (50 * π / 180) - sin (70 * π / 180)) * (sin (130 * π / 180) - sin (110 * π / 180)) = (sin (10 * π / 180)) ^ 2 := by 
    have eq3 : sin (130 * π / 180) = sin (50 * π / 180) := by 
      have h1 : 130 * π / 180 = π - 50 * π / 180 := by 
        linarith [Real.pi_pos]
      rw [h1]
      rw [sin_pi_sub]
    have eq4 : sin (110 * π / 180) = sin (70 * π / 180) := by 
      have h1 : 110 * π / 180 = π - 70 * π / 180 := by 
        linarith [Real.pi_pos]
      rw [h1]
      rw [sin_pi_sub]
    rw [eq3, eq4]
    have eq5 : (sin (50 * π / 180) - sin (70 * π / 180)) * (sin (50 * π / 180) - sin (70 * π / 180)) = (sin (50 * π / 180) - sin (70 * π / 180)) ^ 2 := by 
      ring 
    rw [eq5]
    rw [h6']
    all_goals 
      ring_nf 
  have h20 : (sin (160 * π / 180) + sin (40 * π / 180)) * (sin (140 * π / 180) + sin (20 * π / 180)) + (sin (50 * π / 180) - sin (70 * π / 180)) * (sin (130 * π / 180) - sin (110 * π / 180)) = (cos (10 * π / 180) ) ^ 2 + (sin (10 * π / 180) ) ^ 2 := by
    linarith [eq1, eq2]
  have h21 : (cos (10 * π / 180) ) ^ 2 + (sin (10 * π / 180) ) ^ 2 = 1 := by 
    have h18 : cos (10 * π / 180) ^ 2 + sin (10 * π / 180) ^ 2 = 1 := by 
      exact cos_sq_add_sin_sq (10 * π / 180)
    linarith 
  linarith [h20, h21]