import Mathlib

open Real Set
open scoped Real

theorem algebra_115086 : cos (π/7) - cos (2*π/7) + cos (3*π/7) = 1/2 := by
  have h2 : sin (π / 7) ≠ 0 := by
    apply ne_of_gt
    apply sin_pos_of_pos_of_lt_pi
    linarith [Real.pi_pos]
    linarith [Real.pi_pos]
  have eq2 : sin (π / 7) * (cos (π / 7) - cos (2 * π / 7) + cos (3 * π / 7)) = sin (π / 7) / 2 := by
    have eq3 : sin (π / 7) * (cos (π / 7) - cos (2 * π / 7) + cos (3 * π / 7)) =
        sin (π / 7) * cos (π / 7) - sin (π / 7) * cos (2 * π / 7) + sin (π / 7) * cos (3 * π / 7) := by ring
    rw [eq3]
    have h3 : sin (π / 7) * cos (π / 7) = (1 / 2) * sin (2 * π / 7) := by
      have h1 : sin (π / 7) * cos (π / 7) = (1 / 2) * sin (2 * π / 7) := by
        have h2 : sin (2 * π / 7) = 2 * sin (π / 7) * cos (π / 7) := by
          rw [show 2 * π / 7 = 2 * (π / 7) by ring]
          rw [sin_two_mul]
        linarith
      linarith
    have h5 : sin (π / 7) * cos (2 * π / 7) = (1 / 2) * (sin (3 * π / 7) - sin (π / 7)) := by
      have eq3 : sin (π / 7) * cos (2 * π / 7) = (1 / 2) * (sin (π / 7 + 2 * π / 7) + sin (π / 7 - 2 * π / 7)) := by 
        rw [show π / 7 + 2 * π / 7 = π / 7 + 2 * π / 7 by ring]
        rw [show π / 7 - 2 * π / 7 = π / 7 - 2 * π / 7 by ring]
        rw [sin_add, sin_sub]
        ring
      have h4' : sin (π / 7 - 2 * π / 7) = - sin (π / 7) := by
        have h6 : π / 7 - 2 * π / 7 = - (π / 7) := by
          ring
        rw [h6]
        rw [sin_neg]
      have h7 : π / 7 + 2 * π / 7 = 3 * π / 7 := by 
        ring
      rw [h4', h7] at eq3
      linarith [eq3]
    have h6 : sin (π / 7) * cos (3 * π / 7) = (1 / 2) * (sin (3 * π / 7) - sin (2 * π / 7)) := by
      have eq3 : sin (π / 7) * cos (3 * π / 7) = (1 / 2) * (sin (π / 7 + 3 * π / 7) + sin (π / 7 - 3 * π / 7)) := by 
        rw [show π / 7 + 3 * π / 7 = π / 7 + 3 * π / 7 by ring]
        rw [show π / 7 - 3 * π / 7 = π / 7 - 3 * π / 7 by ring]
        rw [sin_add, sin_sub]
        ring
      have h7' : sin (4 * π / 7) = sin (3 * π / 7) := by
        have h10 : 4 * π / 7 = Real.pi - (3 * π / 7) := by
          ring
        rw [h10]
        rw [sin_pi_sub]
      have h7 : π / 7 + 3 * π / 7 = 4 * π / 7 := by
        ring
      have h8 : π / 7 - 3 * π / 7 = - (2 * π / 7) := by
        ring
      rw [h7, h8] at eq3
      have h9 : sin (-(2 * π / 7)) = - sin (2 * π / 7) := by
        rw [sin_neg]
      rw [h9] at eq3
      linarith [eq3, h7']
    rw [h3, h5, h6]
    ring_nf
    <;> simp [sin_sq, cos_sq] <;> nlinarith [Real.sin_sq_add_cos_sq (π / 7), Real.sin_sq_add_cos_sq (2 * π / 7), Real.sin_sq_add_cos_sq (3 * π / 7)]
  have eq4 : (sin (π / 7) ) ≠ 0 := h2
  apply (mul_left_inj' eq4).mp
  linarith