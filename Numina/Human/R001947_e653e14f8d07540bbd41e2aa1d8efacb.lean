import Mathlib

open Real Set
open scoped Real

/-Prove the identity
cos π/7 * cos 4π/7 * cos5π/7 = 1/8 -/
theorem other_47513 : cos (π/7) * cos (4*π/7) * cos (5*π/7) = 1/8 := by

  have h1 : cos (5 * π / 7) = -cos (2 * π / 7) := by  -- lower the degree
    have h2 : 5 * π / 7 = π - 2 * π / 7 := by ring
    rw [h2]
    rw [cos_pi_sub]
  rw [h1]
  
  rw [show cos (π / 7) * cos (4 * π / 7) * (-cos (2 * π / 7)) 
  = - (cos (π / 7) * cos (2 * π / 7) * cos (4 * π / 7)) by ring]

  have h4 : cos (π / 7) * cos (2 * π / 7) * cos (4 * π / 7) = -1 / 8 := by
      have h5 : sin (8 * (π / 7)) = - sin (π / 7) := by
        have h6 : 8 * (π / 7) = π + π / 7 := by ring
        rw [h6]
        rw [sin_add]
        rw [sin_pi, cos_pi]
        ring
      -- it suffices to prove h7 by expand sin (2x) many times --
      have h7 : sin (8 * (π / 7)) = 8 * sin (π / 7) * cos (π / 7) * cos (2 * π / 7) * cos (4 * π / 7) := by
        have h8 : sin (8 * (π / 7)) = 2 * sin (4 * (π / 7)) * cos (4 * (π / 7)) := by
          have h9 : 8 * (π / 7) = 2 * (4 * (π / 7)) := by ring
          rw [h9]
          rw [sin_two_mul]
        have h10 : sin (4 * (π / 7)) = 2 * sin (2 * (π / 7)) * cos (2 * (π / 7)) := by
          have h11 : 4 * (π / 7) = 2 * (2 * (π / 7)) := by ring
          rw [h11]
          rw [sin_two_mul]
        have h12 : sin (2 * (π / 7)) = 2 * sin (π / 7) * cos (π / 7) := by
          rw [sin_two_mul]
        have h13 : sin (4 * (π / 7)) = 2 * (2 * sin (π / 7) * cos (π / 7)) * cos (2 * (π / 7)) := by
          rw [h10, h12]
        rw [h8, h13]
        ring_nf
      -- for the rest, we need to divide sin (8 * (π / 7)) by sin (π / 7), so we should verify nonzeroness
      have h9 : sin (π / 7) ≠ 0 := by
        have h10 : 0 < π / 7 := by linarith [pi_pos]
        have h11 : π / 7 < π := by linarith [pi_pos]
        have h12 : sin (π / 7) > 0 := by
          apply sin_pos_of_pos_of_lt_pi
          all_goals linarith
        linarith
      rw [h5] at h7
      rw [show cos (π / 7) * cos (2 * π / 7) * cos (4 * π / 7)
      = (8 * sin (π / 7) * cos (π / 7) * cos (2 * π / 7) * cos (4 * π / 7)) / sin (π / 7) * 1/8 by field_simp; ring_nf]
      rw [← h7]
      field_simp
  
  linarith [h4]