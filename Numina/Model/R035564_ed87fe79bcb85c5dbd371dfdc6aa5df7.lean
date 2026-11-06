import Mathlib

open Real Set
open scoped Real

theorem algebra_204848 : arcsin (sin (2000 * π / 180)) = -π / 9 := by
  have h1 : 2000 * π / 180 = 10 * π + 10 * π / 9 := by
    ring
  have h3 : sin (2000 * π / 180) = sin (10 * π / 9) := by
    rw [h1]
    have h5 : sin (10 * π + 10 * π / 9) = sin (10 * π / 9) := by
      have h6 : 10 * π + 10 * π / 9 = (10 * π / 9) + 5 * (2 * π) := by
        ring
      rw [h6]
      have h7 : sin ((10 * π / 9) + 5 * (2 * π)) = sin (10 * π / 9) := by
        have h8 : sin ((10 * π / 9) + 5 * (2 * π)) = sin (10 * π / 9) := by
          have h9 : sin ((10 * π / 9) + 5 * (2 * π)) = sin (10 * π / 9 + 5 * (2 * π)) := by
            ring_nf
          rw [h9]
          have h10 : sin (10 * π / 9 + 5 * (2 * π)) = sin (10 * π / 9) := by
            have h11 : 10 * π / 9 + 5 * (2 * π) = (10 * π / 9) + (5 : ℕ) * (2 * π) := by
              ring_nf
            rw [h11]
            rw [Real.sin_add_nat_mul_two_pi]
          exact h10
        linarith
      linarith
    linarith
  rw [h3]
  have h5 : sin (10 * π / 9) = -sin (π / 9) := by
    have h6 : 10 * π / 9 = π + π / 9 := by
      ring
    rw [h6]
    have h7 : sin (π + π / 9) = -sin (π / 9) := by
      rw [sin_add]
      rw [sin_pi, cos_pi]
      ring
    exact h7
  rw [h5]
  have h7 : arcsin (-sin (π / 9)) = arcsin (sin (-(π / 9))) := by
    have h8 : sin (-(π / 9)) = -sin (π / 9) := by
      rw [sin_neg]
    rw [h8]
  have h10 : arcsin (sin (-(π / 9))) = -(π / 9) := by
    rw [arcsin_sin]
    all_goals
    linarith [pi_pos]
  rw [h7, h10]
  all_goals
  linarith [pi_pos]