import Mathlib

open Real

theorem calculus_11197 : 1 / cos (5 * π / 3) = 2 := by
  have h1 : cos (5 * π / 3) = 1 / 2 := by 
    have h2 : 5 * π / 3 = 2 * π - π / 3 := by
      linarith [Real.pi_pos]
    rw [h2]
    have h3 : cos (2 * π - π / 3) = cos (π / 3) := by
      rw [cos_two_pi_sub]
    rw [h3]
    have h4 : cos (π / 3) = 1 / 2 := by 
      exact Real.cos_pi_div_three
    rw [h4]
  rw [h1]
  field_simp
  <;> linarith [Real.pi_pos]