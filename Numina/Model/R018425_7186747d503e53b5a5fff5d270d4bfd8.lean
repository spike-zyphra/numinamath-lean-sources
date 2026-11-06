import Mathlib

open Real

theorem algebra_164252 : 8 * cos (4 * π / 9) * cos (2 * π / 9) * cos (π / 9) = 1 := by
  have h1 : sin (8 * (π / 9)) = 8 * sin (π / 9) * cos (π / 9) * cos (2 * π / 9) * cos (4 * π / 9) := by
    have h1 : sin (8 * (π / 9)) = 2 * sin (4 * (π / 9)) * cos (4 * (π / 9)) := by 
      rw [show 8 * (π / 9) = 2 * (4 * (π / 9)) by ring]
      rw [sin_two_mul]
    have h2 : sin (4 * (π / 9)) = 2 * sin (2 * (π / 9)) * cos (2 * (π / 9)) := by
      rw [show 4 * (π / 9) = 2 * (2 * (π / 9)) by ring]
      rw [sin_two_mul]
    have h3 : sin (2 * (π / 9)) = 2 * sin (π / 9) * cos (π / 9) := by
      rw [show 2 * (π / 9) = 2 * (π / 9) by ring]
      rw [sin_two_mul]
    rw [h1, h2, h3]
    ring
  have h2 : sin (8 * (π / 9)) = sin (π / 9) := by
    have : 8 * (π / 9) = π - (π / 9) := by
      linarith [Real.pi_pos]
    rw [this]
    rw [sin_pi_sub]
  have h3 : sin (π / 9) ≠ 0 := by
    have h1 : sin (π / 9) > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      linarith [Real.pi_pos]
      linarith [Real.pi_pos]
    linarith
  have eq1 : 8 * cos (π / 9) * cos (2 * π / 9) * cos (4 * π / 9) = 1 := by
    have eq2 : sin (π / 9) = 8 * sin (π / 9) * cos (π / 9) * cos (2 * π / 9) * cos (4 * π / 9) := by
      linarith [h1, h2]
    have eq2' : (8 * cos (π / 9) * cos (2 * π / 9) * cos (4 * π / 9) : ℝ) = 1 := by
      apply (mul_left_inj' h3).mp
      linarith
    linarith
  have eq2 : 8 * cos (4 * π / 9) * cos (2 * π / 9) * cos (π / 9) = 1 := by
    have eq3 : 8 * cos (4 * π / 9) * cos (2 * π / 9) * cos (π / 9) = 8 * cos (π / 9) * cos (2 * π / 9) * cos (4 * π / 9) := by
      ring
    rw [eq3]
    linarith [eq1]
  linarith [eq2]