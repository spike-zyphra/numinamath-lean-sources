import Mathlib

open Real Set
open scoped Real

theorem calculus_22697 : sin (70 * π / 180) * cos (50 * π / 180) +
    sin (260 * π / 180) * cos (280 * π / 180) = sqrt 3 / 4 := by 
  have h1 : sin (260 * π / 180) = -sin (80 * π / 180) := by
    have h1' : 260 * π / 180 = π + 80 * π / 180 := by
      linarith [pi_pos]
    rw [h1']
    rw [show π + 80 * π / 180 = π + (80 * π / 180) by ring]
    rw [sin_add]
    simp [sin_pi, cos_pi]
  have h2 : cos (280 * π / 180) = cos (80 * π / 180) := by
    have h1' : 280 * π / 180 = 2 * π - 80 * π / 180 := by
      linarith [pi_pos]
    rw [h1']
    rw [show 2 * π - 80 * π / 180 = 2 * π - (80 * π / 180) by ring]
    rw [cos_sub]
    simp [cos_two_pi, sin_two_pi]
  -- Transform the original expression using h1 and h2.
  have eq1 : sin (70 * π / 180) * cos (50 * π / 180) + sin (260 * π / 180) * cos (280 * π / 180) =
      sin (70 * π / 180) * cos (50 * π / 180) + (-sin (80 * π / 180)) * cos (80 * π / 180) := by
    rw [h1, h2]
  rw [eq1]
  -- Apply product-to-sum formula
  have eq2 : sin (70 * π / 180) * cos (50 * π / 180) = 1/2 * (sin (120 * π / 180) + sin (20 * π / 180)) := by 
    have h3 : sin (70 * π / 180) * cos (50 * π / 180) = 1/2 * (sin ((70 * π / 180 + 50 * π / 180)) + sin ((70 * π / 180 - 50 * π / 180))) := by
      rw [sin_add, sin_sub]
      ring_nf
    have h4 : 70 * π / 180 + 50 * π / 180 = 120 * π / 180 := by 
      linarith [pi_pos]
    have h5 : 70 * π / 180 - 50 * π / 180 = 20 * π / 180 := by 
      linarith [pi_pos]
    rw [h4, h5] at h3 
    linarith 
  -- Second term transform
  have eq3 : (-sin (80 * π / 180)) * cos (80 * π / 180) = -1/2 * sin (160 * π / 180) := by 
    have h4 : sin (80 * π / 180) * cos (80 * π / 180) = 1/2 * sin (160 * π / 180) := by 
      have h5 : sin (160 * π / 180) = 2 * sin (80 * π / 180) * cos (80 * π / 180) := by 
        rw [show 160 * π / 180 = 2 * (80 * π / 180) by ring]
        rw [sin_two_mul]
      linarith [h5]
    linarith [h4]
  -- Transform the entire expression 
  have eq4 : sin (70 * π / 180) * cos (50 * π / 180) + (-sin (80 * π / 180)) * cos (80 * π / 180) =
      1/2 * (sin (120 * π / 180) + sin (20 * π / 180)) - 1/2 * sin (160 * π / 180) := by 
    rw [eq2, eq3]
    all_goals ring_nf 
  rw [eq4]
  -- Simplify sin(160°) 
  have eq5 : sin (160 * π / 180) = sin (20 * π / 180) := by 
    have h7 : 160 * π / 180 = π - 20 * π / 180 := by 
      linarith [pi_pos]
    rw [h7]
    rw [sin_pi_sub]
  -- Simplify sin(120°) 
  have eq6 : sin (120 * π / 180) = sqrt 3 / 2 := by 
    have h41 : sin (120 * π / 180) = sin (π - (60 * π / 180)) := by 
      ring_nf 
    rw [h41]
    rw [sin_pi_sub]
    -- sin(60°) = sqrt(3)/2
    have h43 : sin (60 * π / 180) = sqrt 3 / 2 := by 
      have h44 : 60 * π / 180 = π / 3 := by 
        linarith [pi_pos]
      rw [h44]
      exact sin_pi_div_three
    linarith 
  rw [eq6, eq5]
  all_goals ring_nf 
  <;> 
    field_simp 
    <;> 
      ring