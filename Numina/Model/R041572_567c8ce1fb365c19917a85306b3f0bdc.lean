import Mathlib

open Real Set
open scoped Real

theorem algebra_2170 : cos (π / 17) * cos (2 * π / 17) * cos (4 * π / 17) * cos (8 * π / 17) = 1 / 16 := by
  have h2 : sin (16 * (π / 17)) = 16 * sin (π / 17) * cos (π / 17) * cos (2 * π / 17) * cos (4 * π / 17) * cos (8 * π / 17) := by
    have h3 : sin (16 * (π / 17)) = 2 * sin (8 * (π / 17)) * cos (8 * (π / 17)) := by
      rw [show 16 * (π / 17) = 2 * (8 * (π / 17)) by ring]
      rw [sin_two_mul]
      <;> ring_nf
    have h4 : sin (8 * (π / 17)) = 2 * sin (4 * (π / 17)) * cos (4 * (π / 17)) := by
      rw [show 8 * (π / 17) = 2 * (4 * (π / 17)) by ring]
      rw [sin_two_mul]
      <;> ring_nf
    have h5 : sin (4 * (π / 17)) = 2 * sin (2 * (π / 17)) * cos (2 * (π / 17)) := by
      rw [show 4 * (π / 17) = 2 * (2 * (π / 17)) by ring]
      rw [sin_two_mul]
      <;> ring_nf
    have h6 : sin (2 * (π / 17)) = 2 * sin (π / 17) * cos (π / 17) := by
      rw [show 2 * (π / 17) = 2 * (π / 17) by ring]
      rw [sin_two_mul]
      <;> ring_nf
    rw [h3, h4, h5, h6]
    ring_nf
  have h8 : sin (16 * (π / 17)) = sin (π - π / 17) := by
    ring_nf
  have h9 : sin (π - π / 17) = sin (π / 17) := by
    rw [sin_pi_sub]
  have h10 : sin (16 * (π / 17)) = sin (π / 17) := by
    rw [h8, h9]
  have h10' : sin (π / 17) = 16 * sin (π / 17) * cos (π / 17) * cos (2 * π / 17) * cos (4 * π / 17) * cos (8 * π / 17) := by
    nlinarith [h2, h10]
  have h11 : sin (π / 17) ≠ 0 := by
    have h12 : π / 17 > 0 := by
      linarith [Real.pi_pos]
    have h13 : π / 17 < π := by
      linarith [Real.pi_pos]
    have h14 : sin (π / 17) > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      all_goals linarith
    linarith
  have h12 : cos (π / 17) * cos (2 * π / 17) * cos (4 * π / 17) * cos (8 * π / 17) = 1 / 16 := by
    apply (mul_left_inj' h11).mp
    linarith
  ring_nf at h12 ⊢
  <;> nlinarith