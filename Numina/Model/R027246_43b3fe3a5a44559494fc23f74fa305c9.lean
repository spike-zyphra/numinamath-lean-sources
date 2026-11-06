import Mathlib

open Real Set
open scoped Real

theorem algebra_307024 : cos (π / 7) + cos (3 * π / 7) + cos (5 * π / 7) = 1 / 2 := by

  have h1 : sin (π / 7) ≠ 0 := by
    have h1 : sin (π / 7) > 0 := by 
      apply sin_pos_of_pos_of_lt_pi 
      all_goals linarith [Real.pi_pos]
    linarith

  have h3 : 2 * sin (π / 7) * (cos (π / 7) + cos (3 * π / 7) + cos (5 * π / 7)) = sin (π / 7) := by 
    have h4 : cos (5 * π / 7) = -cos (2 * π / 7) := by 
      have h3 : 5 * π / 7 = π - 2 * π / 7 := by 
        ring
      rw [h3]
      rw [cos_pi_sub]
    have eq1 : 2 * sin (π / 7) * (cos (π / 7) + cos (3 * π / 7) + cos (5 * π / 7)) = 2 * sin (π / 7) * (cos (π / 7) + cos (3 * π / 7) - cos (2 * π / 7)) := by 
      rw [h4]
      all_goals ring_nf
    have eq1' : 2 * sin (π / 7) * (cos (π / 7) + cos (3 * π / 7) - cos (2 * π / 7)) = sin (π / 7) := by 
      have eq2 : 2 * sin (π / 7) * (cos (π / 7) + cos (3 * π / 7) - cos (2 * π / 7)) =
          2 * sin (π / 7) * cos (π / 7) + 2 * sin (π / 7) * cos (3 * π / 7) - 2 * sin (π / 7) * cos (2 * π / 7) := by ring 
      have eq2' : 2 * sin (π / 7) * cos (π / 7) = sin (2 * (π / 7)) := by 
        rw [sin_two_mul]
      have eq3 : 2 * sin (π / 7) * cos (3 * π / 7) = sin (4 * (π / 7)) - sin (2 * (π / 7)) := by 
        have h8 : 2 * sin (π / 7) * cos (3 * π / 7) = sin ((π / 7) + (3 * π / 7)) + sin ((π / 7) - (3 * π / 7)) := by 
          rw [show (π / 7) + (3 * π / 7) = (π / 7 : ℝ) + (3 * π / 7 : ℝ) by ring]
          rw [show (π / 7) - (3 * π / 7) = (π / 7 : ℝ) - (3 * π / 7 : ℝ) by ring]
          rw [sin_add, sin_sub]
          ring 
        have h9 : (π / 7 : ℝ) + (3 * π / 7) = 4 * (π / 7) := by ring 
        have h10 : (π / 7 : ℝ) - (3 * π / 7) = -(2 * (π / 7)) := by ring 
        rw [h9, h10] at h8 
        have h11 : sin (-(2 * (π / 7))) = -sin (2 * (π / 7)) := by 
          rw [sin_neg]
        rw [h8, h11]
        all_goals ring_nf 
      have eq4 : 2 * sin (π / 7) * cos (2 * π / 7) = sin (3 * π / 7) - sin (π / 7) := by 
        have h5' : 2 * sin (π / 7) * cos (2 * π / 7) = sin (3 * π / 7) - sin (π / 7) := by 
          have h6 : 2 * sin (π / 7) * cos (2 * π / 7) = sin ((π / 7) + (2 * π / 7)) + sin ((π / 7) - (2 * π / 7)) := by 
            rw [show (π / 7) + (2 * π / 7) = (π / 7 : ℝ) + (2 * π / 7 : ℝ) by ring]
            rw [show (π / 7) - (2 * π / 7) = (π / 7 : ℝ) - (2 * π / 7 : ℝ) by ring]
            rw [sin_add, sin_sub]
            ring 
          have h7 : (π / 7 : ℝ) + (2 * π / 7) = 3 * π / 7 := by 
            ring 
          have h8 : (π / 7 : ℝ) - (2 * π / 7) = -(π / 7) := by 
            ring 
          rw [h7, h8] at h6 
          have h9 : sin (-(π / 7)) = -sin (π / 7) := by 
            rw [sin_neg] 
          rw [h9] at h6 
          linarith [h6]
        linarith 
      rw [eq2] 
      have eq5 : sin (4 * (π / 7)) = sin (3 * π / 7) := by 
        have h10 : 4 * (π / 7) = π - (3 * π / 7) := by 
          linarith [Real.pi_pos]
        rw [h10]
        rw [sin_pi_sub]
      have eq6 : sin (2 * (π / 7)) = sin (2 * (π / 7)) := by rfl 
      have eq7 : ( 2 * sin (π / 7) * cos (π / 7) + 2 * sin (π / 7) * cos (3 * π / 7) - 2 * sin (π / 7) * cos (2 * π / 7) ) = sin (π / 7) := by 
        rw [eq2', eq3, eq4] 
        simp only [eq5] 
        ring_nf 
      linarith [eq7] 
    rw [eq1, eq1']
  have h3' : cos (π / 7) + cos (3 * π / 7) + cos (5 * π / 7) = (sin (π / 7) ) / (2 * sin (π / 7) ) := by
    have h3 : 2 * sin (π / 7) * (cos (π / 7) + cos (3 * π / 7) + cos (5 * π / 7)) = sin (π / 7) := h3
    have h4 : sin (π / 7) ≠ 0 := h1 
    field_simp [h4] at *
    nlinarith

  rw [h3']
  have h4 : sin (π / 7) ≠ 0 := h1 
  field_simp [h4]
  all_goals linarith