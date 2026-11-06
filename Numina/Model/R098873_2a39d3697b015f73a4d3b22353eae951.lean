import Mathlib

open Real Set
open scoped Real

theorem calculus_22512 : 1 / sin (330 * π / 180) = -2 := by
  have h1 : sin (330 * π / 180) = -1 / 2 := by
    have h2 : 330 * π / 180 = 2 * π - π / 6 := by 
      linarith [Real.pi_pos]
    rw [h2]
    rw [sin_two_pi_sub]
    have h3 : sin (π / 6) = 1 / 2 := sin_pi_div_six
    linarith [h3]
  rw [h1]
  field_simp