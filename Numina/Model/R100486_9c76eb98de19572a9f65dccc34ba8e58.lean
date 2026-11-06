import Mathlib

open Real Set
open scoped Real

theorem calculus_15450 : (tan (π / 9) ^ 2 - sin (π / 9) ^ 2) / (tan (π / 9) ^ 2 * sin (π / 9) ^ 2) = 1 := by
  have h1 : sin (π / 9) ≠ 0 := by
    have h1 : 0 < π / 9 := by linarith [Real.pi_pos]
    have h2 : sin (π / 9) > 0 := by 
      apply sin_pos_of_pos_of_lt_pi 
      all_goals linarith [Real.pi_pos]
    positivity

  have h1_pos : sin (π / 9) > 0 := by
    have h1 : 0 < π / 9 := by linarith [Real.pi_pos]
    have h2 : sin (π / 9) > 0 := by 
      apply sin_pos_of_pos_of_lt_pi 
      all_goals linarith [Real.pi_pos]
    linarith

  have h2 : cos (π / 9) ≠ 0 := by 
    have h1 : 0 < π / 9 := by linarith [Real.pi_pos]
    have h2 : cos (π / 9) > 0 := by 
      apply cos_pos_of_mem_Ioo
      constructor
      all_goals linarith [Real.pi_pos]
    positivity

  have h2_pos : cos (π / 9) > 0 := by 
    have h1 : 0 < π / 9 := by linarith [Real.pi_pos]
    have h2 : cos (π / 9) > 0 := by 
      apply cos_pos_of_mem_Ioo
      constructor
      all_goals linarith [Real.pi_pos]
    linarith
  
  have htan : tan (π / 9) = sin (π / 9) / cos (π / 9) := by 
    rw [tan_eq_sin_div_cos]

  rw [htan]
  
  field_simp [h1_pos, h2_pos]
  <;> nlinarith [Real.sin_sq_add_cos_sq (π / 9), sq_pos_of_pos (show 0 < sin (π / 9) by linarith), sq_pos_of_pos (show 0 < cos (π / 9) by linarith), mul_pos (show 0 < sin (π / 9) by linarith) (show 0 < cos (π / 9) by linarith)]