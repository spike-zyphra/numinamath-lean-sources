import Mathlib

open Real Set

theorem algebra_9949 : arcsin (sin (2000 * π / 180)) = -20 * π / 180 := by
  have h1 : 2000 * π / 180 = 100 * π / 9 := by
    ring_nf
  have h2 : sin (2000 * π / 180) = - sin (π / 9) := by 
    have h3 : 2000 * π / 180 = π + π / 9 + 5 * (2 * π) := by 
      rw [h1]
      nlinarith [pi_pos]
    rw [h3]
    have h4 : sin (π + π / 9 + 5 * (2 * π)) = sin (π + π / 9) := by 
      have h5 : sin (π + π / 9 + 5 * (2 * π)) = sin (π + π / 9 + (5 : ℕ) * (2 * π)) := by 
        ring_nf
      rw [h5]
      rw [Real.sin_add_nat_mul_two_pi]
    rw [h4]
    have h5 : sin (π + π / 9) = - sin (π / 9) := by 
      rw [sin_add]
      simp [sin_pi, cos_pi]
    rw [h5]
  have h3 : arcsin (sin (2000 * π / 180)) = arcsin (- sin (π / 9)) := by 
    rw [h2]
  have h4 : arcsin (- sin (π / 9)) = - π / 9 := by
    have h5 : arcsin (- sin (π / 9)) = arcsin (sin (- (π / 9))) := by 
      have h6 : sin (- (π / 9)) = - sin (π / 9) := by 
        rw [show - (π / 9) = - (π / 9) by ring]
        rw [sin_neg]
      rw [h6]
    rw [h5]
    have h5 : arcsin (sin (- (π / 9))) = - (π / 9) := by 
      apply arcsin_sin
      all_goals
        linarith [pi_pos]
    linarith
  rw [h3, h4]
  ring_nf