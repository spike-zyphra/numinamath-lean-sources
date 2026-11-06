import Mathlib

open Real Set
open scoped Real

theorem calculus_23283 : cot (π / 2) = 0 := by 
  rw [cot_eq_cos_div_sin]
  have h1 : cos (π / 2) = 0 := by 
    rw [cos_pi_div_two]
  have h2 : sin (π / 2) = 1 := by 
    rw [sin_pi_div_two]
  rw [h1]
  rw [h2]
  all_goals norm_num