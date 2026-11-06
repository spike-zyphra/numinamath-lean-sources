import Mathlib

open Real

theorem calculus_22144 : cos (54 * π / 180) * cos (4 * π / 180) - cos (36 * π / 180) * cos (86 * π / 180) = cos (58 * π / 180) := by
  have h1 : cos (36 * π / 180) = sin (54 * π / 180) := by
    have h2 : 36 * π / 180 = π / 2 - 54 * π / 180 := by
      ring_nf
    rw [h2]
    rw [cos_pi_div_two_sub]
  have h3 : cos (86 * π / 180) = sin (4 * π / 180) := by
    have h4 : 86 * π / 180 = π / 2 - 4 * π / 180 := by
      ring_nf
    rw [h4]
    rw [cos_pi_div_two_sub]
  rw [h1, h3]
  have h5 : cos (54 * π / 180) * cos (4 * π / 180) - sin (54 * π / 180) * sin (4 * π / 180) = cos (54 * π / 180 + 4 * π / 180) := by
    rw [cos_add]
  have h6 : 54 * π / 180 + 4 * π / 180 = 58 * π / 180 := by 
    ring_nf
  rw [h5, h6]
  all_goals linarith