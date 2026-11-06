import Mathlib

open Real Set
open scoped Real

theorem algebra_178122 :
  arccos (sin (-π / 7)) = 9 * π / 14 ∧ arcsin (cos (33 * π / 5)) = -π / 10 := by
  constructor
  · -- Compute arccos (sin (-π / 7))
    have h1 : sin (-π / 7) = cos (9 * π / 14) := by
      have h2 : sin (-π / 7) = - sin (π / 7) := by
        have h3 : sin (-π / 7) = sin (- (π / 7)) := by ring_nf
        rw [h3]
        rw [sin_neg]
        <;> ring_nf
      have h3 : cos (9 * π / 14) = - sin (π / 7) := by
        have h4 : 9 * π / 14 = Real.pi / 2 + π / 7 := by 
          linarith [Real.pi_pos]
        rw [h4]
        rw [cos_add]
        rw [cos_pi_div_two, sin_pi_div_two]
        all_goals ring
      rw [h3, h2]
    rw [h1]
    have h5 : 0 ≤ 9 * π / 14 := by
      nlinarith [Real.pi_pos]
    have h6 : 9 * π / 14 ≤ Real.pi := by
      nlinarith [Real.pi_pos]
    have h7 : arccos (cos (9 * π / 14)) = 9 * π / 14 := by 
      rw [arccos_cos]
      all_goals 
        nlinarith [Real.pi_pos]
    exact h7
  · -- Compute arcsin (cos (33 * π / 5))
    have h8 : cos (33 * π / 5) = - sin (π / 10) := by 
      have h9 : 33 * π / 5 = 6 * π + 3 * π / 5 := by 
        linarith [Real.pi_pos]
      have h10 : cos (33 * π / 5) = cos (3 * π / 5)  := by
        rw [h9]
        have h11 : cos (6 * π + 3 * π / 5) = cos (3 * π / 5) := by
          have h12 : cos (6 * π + 3 * π / 5) = cos (3 * π / 5 + 3 * (2 * π)) := by ring_nf
          rw [h12]
          have h13 : cos (3 * π / 5 + 3 * (2 * π)) = cos (3 * π / 5) := by 
            have h14 : 3 * (2 * π) = (3 : ℕ) * (2 * π) := by ring
            rw [h14]
            rw [cos_add_nat_mul_two_pi]
          exact h13
        exact h11
      have h14 : cos (3 * π / 5) = - sin (π / 10) := by 
        have h15 : 3 * π / 5 = Real.pi / 2 + π / 10 := by 
          linarith [Real.pi_pos]
        rw [h15]
        rw [cos_add]
        rw [cos_pi_div_two, sin_pi_div_two]
        all_goals ring
      rw [h10, h14]
    rw [h8]
    have h10 : arcsin (- sin (π / 10)) = - arcsin (sin (π / 10)) := by 
      rw [arcsin_neg]
    have h11 : arcsin (sin (π / 10)) = π / 10 := by 
      apply arcsin_sin
      all_goals 
        linarith [Real.pi_pos]
    rw [h10, h11]
    all_goals linarith [Real.pi_pos]