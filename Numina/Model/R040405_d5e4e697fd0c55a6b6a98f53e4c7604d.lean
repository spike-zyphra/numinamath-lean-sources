import Mathlib

open Real Set
open scoped Real

theorem algebra_251797 : cos (2 * π / 7) + cos (4 * π / 7) + cos (6 * π / 7) = -1 / 2 := by
  have h1 : sin (π / 7) > 0 := by 
    apply sin_pos_of_pos_of_lt_pi 
    linarith [Real.pi_pos] 
    linarith [Real.pi_pos] 
  have eq1 : sin (π / 7) * (cos (2 * π / 7) + cos (4 * π / 7) + cos (6 * π / 7)) = -1 / 2 * sin (π / 7) := by
    have h2 : sin (π / 7) * cos (2 * π / 7) = 1 / 2 * (sin (3 * π / 7) - sin (π / 7)) := by 
      have h3 : sin (π / 7) * cos (2 * π / 7) = 1 / 2 * (sin ((π / 7 + 2 * π / 7)) + sin ((π / 7 - 2 * π / 7))) := by 
        rw [sin_add, sin_sub]
        ring
      have h4 : π / 7 + 2 * π / 7 = 3 * π / 7 := by ring
      have h5 : π / 7 - 2 * π / 7 = - (π / 7) := by ring
      rw [h4, h5] at h3
      have h6 : sin (- (π / 7)) = - sin (π / 7) := by 
        rw [sin_neg]
      rw [h6] at h3
      linarith [h3]
    have h3 : sin (π / 7) * cos (4 * π / 7) = 1 / 2 * (sin (5 * π / 7) - sin (3 * π / 7)) := by
      have h4 : sin (π / 7) * cos (4 * π / 7) = 1 / 2 * (sin ((π / 7 + 4 * π / 7)) + sin ((π / 7 - 4 * π / 7))) := by
        rw [sin_add, sin_sub]
        ring
      have h5 : π / 7 + 4 * π / 7 = 5 * π / 7 := by ring
      have h6 : π / 7 - 4 * π / 7 = - (3 * π / 7) := by ring
      rw [h5, h6] at h4
      have h7 : sin (- (3 * π / 7)) = - sin (3 * π / 7) := by 
        rw [sin_neg]
      rw [h7] at h4
      linarith [h4]
    have h4 : sin (π / 7) * cos (6 * π / 7) = 1 / 2 * (sin (7 * π / 7) - sin (5 * π / 7)) := by
      have h5 : sin (π / 7) * cos (6 * π / 7) = 1 / 2 * (sin ((π / 7 + 6 * π / 7)) + sin ((π / 7 - 6 * π / 7))) := by
        rw [sin_add, sin_sub]
        ring
      have h6 : π / 7 + 6 * π / 7 = 7 * π / 7 := by ring
      have h7 : π / 7 - 6 * π / 7 = - (5 * π / 7) := by ring
      rw [h6, h7] at h5
      have h8 : sin (- (5 * π / 7)) = - sin (5 * π / 7) := by 
        rw [sin_neg]
      rw [h8] at h5
      linarith [h5]
    calc
      sin (π / 7) * (cos (2 * π / 7) + cos (4 * π / 7) + cos (6 * π / 7))
        = sin (π / 7) * cos (2 * π / 7) + sin (π / 7) * cos (4 * π / 7) + sin (π / 7) * cos (6 * π / 7) := by ring
      _ = 1 / 2 * (sin (3 * π / 7) - sin (π / 7)) + 1 / 2 * (sin (5 * π / 7) - sin (3 * π / 7)) + 1 / 2 * (sin (7 * π / 7) - sin (5 * π / 7)) := by 
        rw [h2, h3, h4]
      _ = 1 / 2 * (sin (3 * π / 7) - sin (π / 7) + sin (5 * π / 7) - sin (3 * π / 7) + sin (7 * π / 7) - sin (5 * π / 7)) := by ring
      _ = 1 / 2 * (- sin (π / 7)) := by 
        have h7 : sin (7 * π / 7) = 0 := by 
          have h8 : 7 * π / 7 = Real.pi := by ring 
          rw [h8] 
          simp
        rw [h7]
        ring_nf
      _ = -1 / 2 * sin (π / 7) := by ring
  have eq2 : cos (2 * π / 7) + cos (4 * π / 7) + cos (6 * π / 7) = -1 / 2 := by
    have h9 : sin (π / 7) > 0 := h1 
    have eq1' : sin (π / 7) * (cos (2 * π / 7) + cos (4 * π / 7) + cos (6 * π / 7)) = -1 / 2 * sin (π / 7) := eq1
    have h10 : sin (π / 7) > 0 := h1 
    have : cos (2 * π / 7) + cos (4 * π / 7) + cos (6 * π / 7) = -1 / 2 := by 
      apply (mul_left_inj' (ne_of_gt h10)).mp
      linarith [eq1']
    exact_mod_cast this 
  exact_mod_cast eq2