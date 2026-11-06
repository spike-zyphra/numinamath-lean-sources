import Mathlib

open Real

theorem calculus_23268 : cos (2 * π / 15) * cos (4 * π / 15) * cos (8 * π / 15) * cos (16 * π / 15) = 1 / 16 := by
  have h1 : cos (16 * π / 15) = -cos (π / 15) := by
    have h2 : 16 * π / 15 = π + π / 15 := by
      linarith [Real.pi_pos]
    rw [h2]
    have h3 : cos (π + π / 15) = -cos (π / 15) := by
      rw [cos_add, cos_pi, sin_pi]
      ring
    exact h3
  have h2 : cos (2 * π / 15) * cos (4 * π / 15) * cos (8 * π / 15) * cos (16 * π / 15) = 
    - (cos (π / 15) * cos (2 * π / 15) * cos (4 * π / 15) * cos (8 * π / 15)) := by
    rw [show cos (16 * π / 15) = -cos (π / 15) by linarith [h1]]
    ring
  have h3 : cos (π / 15) * cos (2 * π / 15) * cos (4 * π / 15) * cos (8 * π / 15) = (sin (16 * π / 15) ) / (16 * sin (π / 15)) := by
    have h4 : sin (16 * π / 15) = 16 * sin (π / 15) * cos (π / 15) * cos (2 * π / 15) * cos (4 * π / 15) * cos (8 * π / 15) := by
      have h1 : sin (16 * π / 15) = 2 * sin (8 * π / 15) * cos (8 * π / 15) := by 
        rw [show 16 * π / 15 = 2 * (8 * π / 15) by ring]
        rw [sin_two_mul]
      have h2 : sin (8 * π / 15) = 2 * sin (4 * π / 15) * cos (4 * π / 15) := by 
        rw [show 8 * π / 15 = 2 * (4 * π / 15) by ring]
        rw [sin_two_mul]
      have h3 : sin (4 * π / 15) = 2 * sin (2 * π / 15) * cos (2 * π / 15) := by 
        rw [show 4 * π / 15 = 2 * (2 * π / 15) by ring]
        rw [sin_two_mul]
      have h4 : sin (2 * π / 15) = 2 * sin (π / 15) * cos (π / 15) := by 
        rw [show 2 * π / 15 = 2 * (π / 15) by ring]
        rw [sin_two_mul]
      rw [h1, h2, h3, h4]
      ring
    have h5 : sin (π / 15) ≠ 0 := by 
      apply ne_of_gt
      apply sin_pos_of_pos_of_lt_pi
      linarith [Real.pi_pos]
      linarith [Real.pi_pos]
    field_simp [h4, h5]
    <;> nlinarith
  have h4 : sin (16 * π / 15) = - sin (π / 15) := by
    have h7 : 16 * π / 15 = π + π / 15 := by
      linarith [Real.pi_pos]
    rw [h7]
    have h8 : sin (π + π / 15) = - sin (π / 15) := by
      rw [sin_add, sin_pi, cos_pi]
      ring
    exact h8
  have h5 : cos (π / 15) * cos (2 * π / 15) * cos (4 * π / 15) * cos (8 * π / 15) = -1 / 16 := by
    rw [h3]
    rw [h4]
    have h6 : sin (π / 15) ≠ 0 := by 
      apply ne_of_gt
      apply sin_pos_of_pos_of_lt_pi
      linarith [Real.pi_pos]
      linarith [Real.pi_pos]
    field_simp [h6]
    <;> nlinarith
  rw [h2, h5]
  all_goals 
    ring