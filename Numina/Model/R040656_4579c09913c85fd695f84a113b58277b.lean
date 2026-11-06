import Mathlib

open Real

theorem calculus_16252 : 1 / cos (120 * π / 180) = -2 := by
  have h1 : 120 * π / 180 = 2 * π / 3 := by
    ring_nf
  rw [h1]
  have h2 : cos (2 * π / 3) = -1 / 2 := by
    have h3 : 2 * π / 3 = π - (π / 3) := by
      ring
    rw [h3]
    rw [cos_pi_sub]
    have h4 : cos (π / 3) = 1 / 2 := by
      exact cos_pi_div_three
    rw [h4]
    all_goals norm_num
  rw [h2]
  field_simp
  <;> norm_num