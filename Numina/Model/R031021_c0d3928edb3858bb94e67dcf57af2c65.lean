import Mathlib

open Real


theorem algebra_425452 : tan (-23 * π / 3) = √3 := by
  have h1a : tan (-23 * π / 3) = tan (Real.pi / 3 - 8 * Real.pi) := by 
    have h2 : -23 * π / 3 = Real.pi / 3 - 8 * Real.pi := by
      linarith [Real.pi_pos]
    rw [h2]
  have h1b : tan (Real.pi / 3 - 8 * Real.pi) = tan (Real.pi / 3) := by
    have h5 : tan (Real.pi / 3 - 8 * Real.pi) = tan (Real.pi / 3 - 7 * Real.pi) := by 
      have h5' : tan (Real.pi / 3 - 8 * Real.pi) = tan ((Real.pi / 3 - 7 * Real.pi) - Real.pi) := by
        ring_nf
      rw [h5']
      rw [tan_sub_pi]
    have h6 : tan (Real.pi / 3 - 7 * Real.pi) = tan (Real.pi / 3 - 6 * Real.pi) := by 
      have h6' : tan (Real.pi / 3 - 7 * Real.pi) = tan ((Real.pi / 3 - 6 * Real.pi) - Real.pi) := by 
        ring_nf
      rw [h6']
      rw [tan_sub_pi]
    have h7 : tan (Real.pi / 3 - 6 * Real.pi) = tan (Real.pi / 3 - 5 * Real.pi) := by 
      have h7' : tan (Real.pi / 3 - 6 * Real.pi) = tan ((Real.pi / 3 - 5 * Real.pi) - Real.pi) := by 
        ring_nf
      rw [h7']
      rw [tan_sub_pi]
    have h8 : tan (Real.pi / 3 - 5 * Real.pi) = tan (Real.pi / 3 - 4 * Real.pi) := by 
      have h8' : tan (Real.pi / 3 - 5 * Real.pi) = tan ((Real.pi / 3 - 4 * Real.pi) - Real.pi) := by 
        ring_nf
      rw [h8']
      rw [tan_sub_pi]
    have h9 : tan (Real.pi / 3 - 4 * Real.pi) = tan (Real.pi / 3 - 3 * Real.pi) := by 
      have h9' : tan (Real.pi / 3 - 4 * Real.pi) = tan ((Real.pi / 3 - 3 * Real.pi) - Real.pi) := by 
        ring_nf
      rw [h9']
      rw [tan_sub_pi]
    have h10 : tan (Real.pi / 3 - 3 * Real.pi) = tan (Real.pi / 3 - 2 * Real.pi) := by 
      have h10' : tan (Real.pi / 3 - 3 * Real.pi) = tan ((Real.pi / 3 - 2 * Real.pi) - Real.pi) := by 
        ring_nf
      rw [h10']
      rw [tan_sub_pi]
    have h11 : tan (Real.pi / 3 - 2 * Real.pi) = tan (Real.pi / 3 - 1 * Real.pi) := by 
      have h11' : tan (Real.pi / 3 - 2 * Real.pi) = tan ((Real.pi / 3 - 1 * Real.pi) - Real.pi) := by 
        ring_nf
      rw [h11']
      rw [tan_sub_pi]
    have h12 : tan (Real.pi / 3 - 1 * Real.pi) = tan (Real.pi / 3) := by
      have h12' : tan (Real.pi / 3 - 1 * Real.pi) = tan ((Real.pi / 3) - Real.pi) := by 
        ring_nf
      rw [h12']
      rw [tan_sub_pi]
    rw [h5, h6, h7, h8, h9, h10, h11, h12]

  have h1 : tan (-23 * π / 3) = tan (Real.pi / 3) := by 
    rw [h1a, h1b]
  have h2 : tan (Real.pi / 3) = Real.sqrt 3 := tan_pi_div_three
  rw [h1, h2]