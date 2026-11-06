import Mathlib

open Real Set
open scoped Real

theorem calculus_12160 : tan (π / 3) = √3 := by 
  have h1 : tan (π / 3) = sin (π / 3) / cos (π / 3) := by
    rw [tan_eq_sin_div_cos]
  rw [h1]
  have h2 : sin (π / 3) = Real.sqrt 3 / 2 := by
    exact sin_pi_div_three
  have h3 : cos (π / 3) = 1 / 2 := by
    exact cos_pi_div_three
  rw [h2, h3]
  field_simp